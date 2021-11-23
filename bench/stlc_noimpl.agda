
{-# OPTIONS --type-in-type #-}

Ty% : Set
Ty% =
   (Ty%         : Set)
   (nat top bot  : Ty%)
   (arr prod sum : Ty% → Ty% → Ty%)
 → Ty%

nat% : Ty%; nat% = λ _ nat% _ _ _ _ _ → nat%
top% : Ty%; top% = λ _ _ top% _ _ _ _ → top%
bot% : Ty%; bot% = λ _ _ _ bot% _ _ _ → bot%

arr% : Ty% → Ty% → Ty%; arr%
 = λ A B Ty% nat% top% bot% arr% prod sum →
     arr% (A Ty% nat% top% bot% arr% prod sum) (B Ty% nat% top% bot% arr% prod sum)

prod% : Ty% → Ty% → Ty%; prod%
 = λ A B Ty% nat% top% bot% arr% prod% sum →
     prod% (A Ty% nat% top% bot% arr% prod% sum) (B Ty% nat% top% bot% arr% prod% sum)

sum% : Ty% → Ty% → Ty%; sum%
 = λ A B Ty% nat% top% bot% arr% prod% sum% →
     sum% (A Ty% nat% top% bot% arr% prod% sum%) (B Ty% nat% top% bot% arr% prod% sum%)

Con% : Set; Con%
 = (Con% : Set)
   (nil  : Con%)
   (snoc : Con% → Ty% → Con%)
 → Con%

nil% : Con%; nil%
 = λ Con% nil% snoc → nil%

snoc% : Con% → Ty% → Con%; snoc%
 = λ Γ A Con% nil% snoc% → snoc% (Γ Con% nil% snoc%) A

Var% : Con% → Ty% → Set; Var%
 = λ Γ A →
   (Var% : Con% → Ty% → Set)
   (vz  : ∀ Γ A → Var% (snoc% Γ A) A)
   (vs  : ∀ Γ B A → Var% Γ A → Var% (snoc% Γ B) A)
 → Var% Γ A

vz% : ∀{Γ A} → Var% (snoc% Γ A) A; vz%
 = λ Var% vz% vs → vz% _ _

vs% : ∀{Γ B A} → Var% Γ A → Var% (snoc% Γ B) A; vs%
 = λ x Var% vz% vs% → vs% _ _ _ (x Var% vz% vs%)

Tm% : Con% → Ty% → Set; Tm%
 = λ Γ A →
   (Tm%  : Con% → Ty% → Set)
   (var   : ∀ Γ A      → Var% Γ A → Tm% Γ A)
   (lam   : ∀ Γ A B    → Tm% (snoc% Γ A) B → Tm% Γ (arr% A B))
   (app   : ∀ Γ A B    → Tm% Γ (arr% A B) → Tm% Γ A → Tm% Γ B)
   (tt    : ∀ Γ        → Tm% Γ top%)
   (pair  : ∀ Γ A B    → Tm% Γ A → Tm% Γ B → Tm% Γ (prod% A B))
   (fst   : ∀ Γ A B    → Tm% Γ (prod% A B) → Tm% Γ A)
   (snd   : ∀ Γ A B    → Tm% Γ (prod% A B) → Tm% Γ B)
   (left  : ∀ Γ A B    → Tm% Γ A → Tm% Γ (sum% A B))
   (right : ∀ Γ A B    → Tm% Γ B → Tm% Γ (sum% A B))
   (case  : ∀ Γ A B C  → Tm% Γ (sum% A B) → Tm% Γ (arr% A C) → Tm% Γ (arr% B C) → Tm% Γ C)
   (zero  : ∀ Γ        → Tm% Γ nat%)
   (suc   : ∀ Γ        → Tm% Γ nat% → Tm% Γ nat%)
   (rec   : ∀ Γ A      → Tm% Γ nat% → Tm% Γ (arr% nat% (arr% A A)) → Tm% Γ A → Tm% Γ A)
 → Tm% Γ A

var% : ∀{Γ A} → Var% Γ A → Tm% Γ A; var%
 = λ x Tm% var% lam app tt pair fst snd left right case zero suc rec →
     var% _ _ x

lam% : ∀{Γ A B} → Tm% (snoc% Γ A) B → Tm% Γ (arr% A B); lam%
 = λ t Tm% var% lam% app tt pair fst snd left right case zero suc rec →
     lam% _ _ _ (t Tm% var% lam% app tt pair fst snd left right case zero suc rec)

app% : ∀{Γ A B} → Tm% Γ (arr% A B) → Tm% Γ A → Tm% Γ B; app%
 = λ t u Tm% var% lam% app% tt pair fst snd left right case zero suc rec →
     app% _ _ _ (t Tm% var% lam% app% tt pair fst snd left right case zero suc rec)
         (u Tm% var% lam% app% tt pair fst snd left right case zero suc rec)

tt% : ∀{Γ} → Tm% Γ top%; tt%
 = λ Tm% var% lam% app% tt% pair fst snd left right case zero suc rec → tt% _

pair% : ∀{Γ A B} → Tm% Γ A → Tm% Γ B → Tm% Γ (prod% A B); pair%
 = λ t u Tm% var% lam% app% tt% pair% fst snd left right case zero suc rec →
     pair% _ _ _ (t Tm% var% lam% app% tt% pair% fst snd left right case zero suc rec)
          (u Tm% var% lam% app% tt% pair% fst snd left right case zero suc rec)

fst% : ∀{Γ A B} → Tm% Γ (prod% A B) → Tm% Γ A; fst%
 = λ t Tm% var% lam% app% tt% pair% fst% snd left right case zero suc rec →
     fst% _ _ _ (t Tm% var% lam% app% tt% pair% fst% snd left right case zero suc rec)

snd% : ∀{Γ A B} → Tm% Γ (prod% A B) → Tm% Γ B; snd%
 = λ t Tm% var% lam% app% tt% pair% fst% snd% left right case zero suc rec →
     snd% _ _ _ (t Tm% var% lam% app% tt% pair% fst% snd% left right case zero suc rec)

left% : ∀{Γ A B} → Tm% Γ A → Tm% Γ (sum% A B); left%
 = λ t Tm% var% lam% app% tt% pair% fst% snd% left% right case zero suc rec →
     left% _ _ _ (t Tm% var% lam% app% tt% pair% fst% snd% left% right case zero suc rec)

right% : ∀{Γ A B} → Tm% Γ B → Tm% Γ (sum% A B); right%
 = λ t Tm% var% lam% app% tt% pair% fst% snd% left% right% case zero suc rec →
     right% _ _ _ (t Tm% var% lam% app% tt% pair% fst% snd% left% right% case zero suc rec)

case% : ∀{Γ A B C} → Tm% Γ (sum% A B) → Tm% Γ (arr% A C) → Tm% Γ (arr% B C) → Tm% Γ C; case%
 = λ t u v Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero suc rec →
     case% _ _ _ _
           (t Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero suc rec)
           (u Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero suc rec)
           (v Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero suc rec)

zero%  : ∀{Γ} → Tm% Γ nat%; zero%
 = λ Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero% suc rec → zero% _

suc% : ∀{Γ} → Tm% Γ nat% → Tm% Γ nat%; suc%
 = λ t Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero% suc% rec →
   suc% _ (t Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero% suc% rec)

rec% : ∀{Γ A} → Tm% Γ nat% → Tm% Γ (arr% nat% (arr% A A)) → Tm% Γ A → Tm% Γ A; rec%
 = λ t u v Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero% suc% rec% →
     rec% _ _
          (t Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero% suc% rec%)
          (u Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero% suc% rec%)
          (v Tm% var% lam% app% tt% pair% fst% snd% left% right% case% zero% suc% rec%)

v0% : ∀{Γ A} → Tm% (snoc% Γ A) A; v0%
 = var% vz%

v1% : ∀{Γ A B} → Tm% (snoc% (snoc% Γ A) B) A; v1%
 = var% (vs% vz%)

v2% : ∀{Γ A B C} → Tm% (snoc% (snoc% (snoc% Γ A) B) C) A; v2%
 = var% (vs% (vs% vz%))

v3% : ∀{Γ A B C D} → Tm% (snoc% (snoc% (snoc% (snoc% Γ A) B) C) D) A; v3%
 = var% (vs% (vs% (vs% vz%)))

tbool% : Ty%; tbool%
 = sum% top% top%

true% : ∀{Γ} → Tm% Γ tbool%; true%
 = left% tt%

tfalse% : ∀{Γ} → Tm% Γ tbool%; tfalse%
 = right% tt%

ifthenelse% : ∀{Γ A} → Tm% Γ (arr% tbool% (arr% A (arr% A A))); ifthenelse%
 = lam% (lam% (lam% (case% v2% (lam% v2%) (lam% v1%))))

times4% : ∀{Γ A} → Tm% Γ (arr% (arr% A A) (arr% A A)); times4%
  = lam% (lam% (app% v1% (app% v1% (app% v1% (app% v1% v0%)))))

add% : ∀{Γ} → Tm% Γ (arr% nat% (arr% nat% nat%)); add%
 = lam% (rec% v0%
       (lam% (lam% (lam% (suc% (app% v1% v0%)))))
       (lam% v0%))

mul% : ∀{Γ} → Tm% Γ (arr% nat% (arr% nat% nat%)); mul%
 = lam% (rec% v0%
       (lam% (lam% (lam% (app% (app% add% (app% v1% v0%)) v0%))))
       (lam% zero%))

fact% : ∀{Γ} → Tm% Γ (arr% nat% nat%); fact%
 = lam% (rec% v0% (lam% (lam% (app% (app% mul% (suc% v1%)) v0%)))
        (suc% zero%))
