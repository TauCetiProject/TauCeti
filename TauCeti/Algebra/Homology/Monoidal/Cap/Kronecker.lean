/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.Algebra.Homology.Monoidal.Cap.Basic
public import TauCeti.Algebra.Homology.Monoidal.Cup

/-!
# The Kronecker pairing of cap and cup products

Let `D : E ⟶ A ⊗ B` be a diagonal of chain complexes in a `k`-linear monoidal category, let
`a : M ⊗ B ⟶ B'` be an action of the coefficient object `M`, and let `ν : M ⊗ N ⟶ N'` be a pairing
of coefficient objects.  Suppose that a cochain `ψ : B'_q ⟶ N'` and a cochain `ψ' : B_q ⟶ N` are
compatible with the action and the pairing, `a ≫ ψ = (M ◁ ψ') ≫ ν`.  Then evaluating `ψ` on the
cap product of a chain `x` of `E` with a cochain `φ : A_p ⟶ M` is evaluating the cup product of
`φ` and `ψ'` along `D` and `ν` on `x`:

`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ', x⟩`,

with no sign, since both sides take the component of `D` and project to the summand
`A_p ⊗ B_q`.  On homology, for cocycles `φ`, `ψ` and `ψ'`, the cap product with the class of `φ`
followed by the Kronecker map of the class of `ψ` is the Kronecker map of the cup product of the
classes of `φ` and `ψ'`.

For singular chains, `TopCat.singularCap_comp_singularKronecker` is the case `M = 𝟙_ C`,
`N' = N` arbitrary and `ν = (λ_ N).hom`, with `B' = B = C(X; S)`, `a` the chain map induced by the
left unitor of `S` (in each degree the left unitor of the object of chains) and `ψ' = ψ`.

On classes the compatibility of `ψ` and `ψ'` is expressed through the map of cochain complexes
`Hom(B, N) ⟶ Hom(M ⊗ B, N')`, `ψ' ↦ (M ◁ ψ') ≫ ν`: the identity holds for classes `ψ` and `β` such
that the pull-back of `ψ` along `a` is the image of `β` under this map.

## Main results

* `TauCeti.ChainComplex.capChain_comp`: the identity `⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ', x⟩` of cochains.
* `TauCeti.ChainComplex.cap_comp_kronecker`: the identity on homology classes and cocycles.
* `ChainComplex.linearYonedaObjWhiskerLeft`: the extension of cochains along `ν`.
* `TauCeti.ChainComplex.cap_comp_kronecker_linearYonedaObjWhiskerLeft` and
  `TauCeti.ChainComplex.cap_comp_kronecker_of_homologyMap_eq`: the identity on homology and
  cohomology classes, for the identity action and for a general action.
* `TauCeti.ChainComplex.cap_comp_kronecker_of_isIso`: for an invertible action, every class `β`
  has an extension to evaluate, through the inverse of the action.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the identity `ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ)` relating the cap and cup products.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Chain

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] {A B B' E : ChainComplex C ℕ}
  [A.HasTensor B] {M N N' : C} {k : Type*} [CommSemiring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B') (ν : M ⊗ N ⟶ N')

/-- **The Kronecker pairing of a cap product of chains and cochains**,
`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ', x⟩`: if the cochain `ψ : B'_q ⟶ N'` is obtained from `ψ' : B_q ⟶ N`
through the action `a` and the pairing `ν`, then the cap product with `φ` followed by `ψ` is the
cup product of `φ` and `ψ'` along `D` and `ν`. -/
lemma capChain_comp (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B'.X q ⟶ N')
    (ψ' : B.X q ⟶ N) (hψ : a.f q ≫ ψ = (M ◁ ψ') ≫ ν) :
    capChain k D a p q n h φ ≫ ψ = cupCochain k D ν p q n h φ ψ' := by
  rw [capChain_apply, cupCochain_apply, Category.assoc, tensorCochain_comp, hψ,
    tensorCochain_whiskerLeft_comp, Category.id_comp]

end Chain

end TauCeti.ChainComplex

namespace ChainComplex

section Whisker

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C] {M N N' : C}

variable (k M) in
/-- **Extension of cochains along a coefficient pairing**: for a pairing `ν : M ⊗ N ⟶ N'`, the map
of cochain complexes `Hom(B, N) ⟶ Hom(M ⊗ B, N')` sending a cochain `ψ` to `(M ◁ ψ) ≫ ν`. -/
def linearYonedaObjWhiskerLeft (B : ChainComplex C ℕ) (ν : M ⊗ N ⟶ N') :
    B.linearYonedaObj k N ⟶
      ChainComplex.linearYonedaObj (((tensorLeft M).mapHomologicalComplex _).obj B) k N' where
  f i := ModuleCat.ofHom
    { toFun ψ := (M ◁ (ψ : B.X i ⟶ N)) ≫ ν
      map_add' ψ ψ' := (congrArg (· ≫ ν) (MonoidalPreadditive.whiskerLeft_add (X := M)
        (ψ : B.X i ⟶ N) ψ')).trans (Preadditive.add_comp _ _ _ _ _ ν)
      map_smul' r ψ := (congrArg (· ≫ ν) (MonoidalLinear.whiskerLeft_smul M r
        (ψ : B.X i ⟶ N))).trans (Linear.smul_comp _ _ _ r _ ν) }
  comm' i j _ := by
    ext (ψ : B.X i ⟶ N)
    exact (MonoidalCategory.whiskerLeft_comp_assoc M (B.d j i) ψ ν).symm

/-- The extension of a cochain `ψ` along a pairing `ν` is `(M ◁ ψ) ≫ ν`. -/
@[simp↓]
lemma linearYonedaObjWhiskerLeft_f_hom_apply (B : ChainComplex C ℕ) (ν : M ⊗ N ⟶ N') (i : ℕ)
    (ψ : B.X i ⟶ N) :
    (B.linearYonedaObjWhiskerLeft k M ν).f i ψ = (M ◁ ψ) ≫ ν :=
  (rfl)

/-- The extension along `ν` sends the class of a cocycle to the class of its extension. -/
@[simp]
lemma homologyMap_linearYonedaObjWhiskerLeft_homologyπ_apply (B : ChainComplex C ℕ)
    (ν : M ⊗ N ⟶ N') (i : ℕ) (ψ : (B.linearYonedaObj k N).cycles i) :
    homologyMap (B.linearYonedaObjWhiskerLeft k M ν) i ((B.linearYonedaObj k N).homologyπ i ψ) =
      (ChainComplex.linearYonedaObj (((tensorLeft M).mapHomologicalComplex _).obj B) k N').homologyπ
        i (cyclesMap (B.linearYonedaObjWhiskerLeft k M ν) i ψ) :=
  ConcreteCategory.congr_hom (homologyπ_naturality _ i) ψ

/-- The extension along `ν` of a cocycle `ψ` is `(M ◁ ψ) ≫ ν`. -/
@[simp↓]
lemma iCycles_cyclesMap_linearYonedaObjWhiskerLeft_apply (B : ChainComplex C ℕ)
    (ν : M ⊗ N ⟶ N') (i : ℕ) (ψ : (B.linearYonedaObj k N).cycles i) :
    (ChainComplex.linearYonedaObj (((tensorLeft M).mapHomologicalComplex _).obj B) k N').iCycles i
        (cyclesMap (B.linearYonedaObjWhiskerLeft k M ν) i ψ) =
      (M ◁ (B.linearYonedaObj k N).iCycles i ψ) ≫ ν :=
  (ConcreteCategory.congr_hom (cyclesMap_i _ i) ψ).trans
    (B.linearYonedaObjWhiskerLeft_f_hom_apply ν i _)

end Whisker

end ChainComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Homology

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] {A B B' E : ChainComplex C ℕ}
  [A.HasTensor B] {M N N' : C} {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B') (ν : M ⊗ N ⟶ N')

/-- **The Kronecker pairing of a cap product on homology**, `⟨[ψ], x ⌢ [φ]⟩ = ⟨[φ] ⌣ [ψ'], x⟩`:
if the cocycle `ψ` of `Hom(B', N')` is obtained from the cocycle `ψ'` of `Hom(B, N)` through the
action `a` and the pairing `ν`, then capping with the class of `φ` and applying the Kronecker map
of the class of `ψ` is the Kronecker map of the cup product of the classes of `φ` and `ψ'`. -/
lemma cap_comp_kronecker (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).cycles p)
    (ψ : (B'.linearYonedaObj k N').cycles q) (ψ' : (B.linearYonedaObj k N).cycles q)
    (hψ : a.f q ≫ (B'.linearYonedaObj k N').iCycles q ψ =
      (M ◁ (B.linearYonedaObj k N).iCycles q ψ') ≫ ν) :
    cap k D a p q n h ((A.linearYonedaObj k M).homologyπ p φ) ≫
        kronecker k B' N' q ((B'.linearYonedaObj k N').homologyπ q ψ) =
      kronecker k E N' n (cup k D ν p q n h ((A.linearYonedaObj k M).homologyπ p φ)
        ((B.linearYonedaObj k N).homologyπ q ψ')) := by
  rw [← cancel_epi (E.homologyπ n), cap_homologyπ_assoc, kronecker_homologyπ, cup_homologyπ,
    kronecker_homologyπ, iCycles_cupCycles]
  exact (capCycles_i_assoc D a p q n h φ _).trans
    (congrArg (E.iCycles n ≫ ·) (capChain_comp D a ν p q n h _ _ _ hψ))

/-- **The Kronecker pairing of a cap product with an extended class**,
`⟨ν(M ⊗ β), x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: capping with a class `α ∈ Hᵖ(Hom(A, M))` along the diagonal `D`
and the identity action of `M`, into `H_q(M ⊗ B)`, and then evaluating the extension of a class
`β ∈ H^q(Hom(B, N))` along the pairing `ν`, is evaluating the cup product of `α` and `β` along `D`
and `ν`. -/
lemma cap_comp_kronecker_linearYonedaObjWhiskerLeft (p q n : ℕ) (h : p + q = n)
    (α : (A.linearYonedaObj k M).homology p) (β : (B.linearYonedaObj k N).homology q) :
    cap k D (𝟙 _) p q n h α ≫ kronecker k _ N' q
        (homologyMap (B.linearYonedaObjWhiskerLeft k M ν) q β) =
      kronecker k E N' n (cup k D ν p q n h α β) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [ChainComplex.homologyMap_linearYonedaObjWhiskerLeft_homologyπ_apply]
  refine cap_comp_kronecker D (𝟙 _) ν p q n h φ _ ψ ?_
  rw [ChainComplex.iCycles_cyclesMap_linearYonedaObjWhiskerLeft_apply, HomologicalComplex.id_f]
  exact Category.id_comp _

/-- **The Kronecker pairing of a cap product on homology classes**, `⟨ψ, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`:
if the pull-back along the action `a : M ⊗ B ⟶ B'` of a class `ψ ∈ H^q(Hom(B', N'))` is the
extension along the pairing `ν` of a class `β ∈ H^q(Hom(B, N))`, then capping with a class `α`
along `D` and `a` and evaluating `ψ` is evaluating the cup product of `α` and `β` along `D` and
`ν`.  This is the class-level form of `TauCeti.ChainComplex.cap_comp_kronecker`. -/
lemma cap_comp_kronecker_of_homologyMap_eq (p q n : ℕ) (h : p + q = n)
    (α : (A.linearYonedaObj k M).homology p) (ψ : (B'.linearYonedaObj k N').homology q)
    (β : (B.linearYonedaObj k N).homology q)
    (hψ : homologyMap (K := B'.linearYonedaObj k N')
        (L := ChainComplex.linearYonedaObj (((tensorLeft M).mapHomologicalComplex _).obj B) k N')
        ((linearYonedaFunctor k N').map a.op) q ψ =
      homologyMap (B.linearYonedaObjWhiskerLeft k M ν) q β) :
    cap k D a p q n h α ≫ kronecker k B' N' q ψ =
      kronecker k E N' n (cup k D ν p q n h α β) := by
  have hcap := cap_naturality D a D (𝟙 _) (𝟙 E) (𝟙 A) (𝟙 B) a (by simp) (by simp) p q n h α
  simp only [op_id, CategoryTheory.Functor.map_id, linearYonedaFunctor_obj, homologyMap_id,
    ModuleCat.hom_id, LinearMap.id_coe, id_eq, Category.id_comp] at hcap
  rw [← hcap, Category.assoc, ← kronecker_naturality, hψ,
    cap_comp_kronecker_linearYonedaObjWhiskerLeft]

/-- **The Kronecker pairing of a cap product along an invertible action**,
`⟨ν(M ⊗ β), x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: when the action `a : M ⊗ B ⟶ B'` is invertible, every class
`β ∈ H^q(Hom(B, N))` extends along `ν` to a class of `H^q(Hom(B', N'))`, through the inverse of
`a`, and evaluating it on the cap product with `α` along `D` and `a` is evaluating the cup product
of `α` and `β` along `D` and `ν`. -/
lemma cap_comp_kronecker_of_isIso [IsIso a] (p q n : ℕ) (h : p + q = n)
    (α : (A.linearYonedaObj k M).homology p) (β : (B.linearYonedaObj k N).homology q) :
    cap k D a p q n h α ≫ kronecker k B' N' q
        (homologyMap (K := ChainComplex.linearYonedaObj
            (((tensorLeft M).mapHomologicalComplex _).obj B) k N')
          (L := B'.linearYonedaObj k N') ((linearYonedaFunctor k N').map (inv a).op) q
          (homologyMap (B.linearYonedaObjWhiskerLeft k M ν) q β)) =
      kronecker k E N' n (cup k D ν p q n h α β) := by
  refine cap_comp_kronecker_of_homologyMap_eq D a ν p q n h α _ β ?_
  exact (homologyMapIso ((linearYonedaFunctor k N').mapIso (asIso a).op) q).inv_hom_id_apply _

end Homology

end TauCeti.ChainComplex
