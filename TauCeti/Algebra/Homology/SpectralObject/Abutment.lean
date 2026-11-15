/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import TauCeti.Algebra.Homology.SpectralObject.Stabilization

/-!
# The abutment of a spectral object indexed by `EInt` and its filtration

Let `X` be a spectral object in an abelian category, indexed by `EInt`. Its abutment in degree
`n` is `H^n(⊥ ≤ ⊤)` (`X.abutment n`), for a filtered complex the cohomology of the complex. It is
filtered by the images of the maps `H^n(⊥ ≤ q) ⟶ H^n(⊥ ≤ ⊤)`: the `q`th piece is
`opZ^n(⊥ ≤ q, q ≤ ⊤)`, the cokernel of `δ : H^{n-1}(q ≤ ⊤) ⟶ H^n(⊥ ≤ q)`, embedded in the abutment
by `X.abutmentFiltrationι q n` (a monomorphism, by exactness). The pieces increase with `q`
(`X.abutmentFiltrationMap q n`, a monomorphism fitting into a short exact sequence with its
cokernel via `shortExact_abutmentFiltrationMap`), and the limit object
`X.EInfty q n = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` of the spectral sequence is the graded piece: the cokernel
of `F_q H^n ⟶ F_{q+1} H^n` (`X.EInftyIsoCokernel`), from Mathlib's short exact sequence
`shortComplexOpcyclesThreeδ₂Toδ₁_shortExact`.

The filtration is bounded below and exhaustive in degree `n` as soon as `H^n(⊥ ≤ q)` vanishes for
small `q` (`isZero_abutmentFiltration`) and `H^n(q ≤ ⊤)` vanishes for large `q`
(`isIso_abutmentFiltrationι`). When `F_a H^n` vanishes and every graded piece on `Ico a b`
vanishes, `F_b H^n` and (once exhaustive at `b`) `X.abutment n` vanish
(`isZero_abutmentFiltration_of_forall_isZero_cokernel`,
`isZero_abutment_of_forall_isZero_cokernel`).

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.abutment X n`: the object `H^n(⊥ ≤ ⊤)`.
* `CategoryTheory.Abelian.SpectralObject.abutmentFiltration X q n`: the `q`th filtration piece.
* `CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel X q n`: `E∞` is the graded piece
  (characterized by `opcyclesToE_EInftyIsoCokernel_hom`).
* `CategoryTheory.Abelian.SpectralObject.shortExact_abutmentFiltrationMap` and
  `CategoryTheory.Abelian.SpectralObject.isZero_abutment_of_forall_isZero_cokernel`: short
  exactness of each filtration step and vanishing of a finitely filtered abutment from its graded
  pieces.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C EInt)

/-- The abutment `H^n(⊥ ≤ ⊤)` of a spectral object indexed by `EInt`. -/
noncomputable abbrev abutment (n : ℤ) : C :=
  (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))

/-- The `q`th piece `opZ^n(⊥ ≤ q, q ≤ ⊤)` of the filtration of the abutment in degree `n`: the
cokernel of `δ : H^{n-1}(q ≤ ⊤) ⟶ H^n(⊥ ≤ q)`, that is, the image of `H^n(⊥ ≤ q)` in the
abutment. -/
noncomputable abbrev abutmentFiltration (q n : ℤ) : C :=
  X.opcycles (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (le_top : (q : EInt) ≤ ⊤)) n

/-- The embedding of the `q`th filtration piece into the abutment. -/
noncomputable def abutmentFiltrationι (q n : ℤ) : X.abutmentFiltration q n ⟶ X.abutment n :=
  X.fromOpcycles _ _ _ (Subsingleton.elim _ _) n

lemma abutmentFiltrationι_eq (q n : ℤ) :
    X.abutmentFiltrationι q n = X.fromOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (le_top : (q : EInt) ≤ ⊤)) (homOfLE bot_le) (Subsingleton.elim _ _) n := by
  rw [abutmentFiltrationι]

/-- The embedding of the `q`th filtration piece is induced by the map `H^n(⊥ ≤ q) ⟶ H^n(⊥ ≤ ⊤)`. -/
@[reassoc (attr := simp)]
lemma pOpcycles_abutmentFiltrationι (q n : ℤ) :
    X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (le_top : (q : EInt) ≤ ⊤)) n ≫
      X.abutmentFiltrationι q n =
    (X.H n).map (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (le_top : (q : EInt) ≤ ⊤)) (homOfLE bot_le) (Subsingleton.elim _ _)) := by
  rw [abutmentFiltrationι_eq, p_fromOpcycles]

instance (q n : ℤ) : Mono (X.abutmentFiltrationι q n) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1
    (X.exact₁ _ _ _ (Subsingleton.elim _ _) (n - 1) n)

/-- The inclusion of the `q`th filtration piece into the `(q + 1)`st one. -/
noncomputable def abutmentFiltrationMap (q n : ℤ) :
    X.abutmentFiltration q n ⟶ X.abutmentFiltration (q + 1) n :=
  X.opcyclesMap _ _ _ _ (threeδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (coe_le_coe_add_one q)) (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
    (homOfLE bot_le) (homOfLE le_top) (Subsingleton.elim _ _) (Subsingleton.elim _ _)) n

@[reassoc (attr := simp)]
lemma abutmentFiltrationMap_ι (q n : ℤ) :
    X.abutmentFiltrationMap q n ≫ X.abutmentFiltrationι (q + 1) n =
      X.abutmentFiltrationι q n := by
  dsimp [abutmentFiltrationMap, abutmentFiltrationι]
  rw [X.opcyclesMap_fromOpcycles _ _ _ _ _ _ _ _ _ (𝟙 _) n (by simp [threeδ₂Toδ₁])
    (by simp [threeδ₂Toδ₁]), CategoryTheory.Functor.map_id, Category.comp_id]

instance (q n : ℤ) : Mono (X.abutmentFiltrationMap q n) :=
  mono_of_mono_fac (X.abutmentFiltrationMap_ι q n)

/-- Each step `F_q H^n ⟶ F_{q+1} H^n` of the filtration of the abutment fits into a short exact
sequence with its cokernel. -/
theorem shortExact_abutmentFiltrationMap (q n : ℤ) :
    (ShortComplex.mk (X.abutmentFiltrationMap q n)
      (cokernel.π (X.abutmentFiltrationMap q n)) (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

/-- If `F_a H^n` is zero and every graded piece `F_{q+1} H^n / F_q H^n` for `a ≤ q < b` is zero,
then `F_b H^n` is zero. -/
theorem isZero_abutmentFiltration_of_forall_isZero_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a n))
    (hcok : ∀ q ∈ Finset.Ico a b, IsZero (cokernel (X.abutmentFiltrationMap q n))) :
    IsZero (X.abutmentFiltration b n) := by
  induction b, hab using Int.leInduction with
  | base => exact ha
  | succ q haq ih =>
    exact (X.shortExact_abutmentFiltrationMap q n).exact.isZero_of_both_isZero
      (ih fun i hi ↦ hcok i (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hi))
      (hcok q (Finset.mem_Ico.2 ⟨haq, Int.lt_add_one_iff.2 le_rfl⟩))

/-- If the filtration of `X.abutment n` starts at `0` at `a`, exhausts the abutment at `b ≥ a`, and
has vanishing graded pieces on `Ico a b`, then `X.abutment n` is zero. -/
theorem isZero_abutment_of_forall_isZero_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a n)) (hb : IsIso (X.abutmentFiltrationι b n))
    (hcok : ∀ q ∈ Finset.Ico a b, IsZero (cokernel (X.abutmentFiltrationMap q n))) :
    IsZero (X.abutment n) :=
  have := hb
  (X.isZero_abutmentFiltration_of_forall_isZero_cokernel hab ha hcok).of_iso
    (asIso (X.abutmentFiltrationι b n)).symm

/-- The limit object `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` of the spectral sequence is the graded piece
`F_{q+1} H^n / F_q H^n` of the filtration of the abutment. -/
noncomputable def EInftyIsoCokernel (q n : ℤ) :
    X.EInfty q n ≅ cokernel (X.abutmentFiltrationMap q n) :=
  (X.shortComplexOpcyclesThreeδ₂Toδ₁_shortExact (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (coe_le_coe_add_one q)) (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
    (homOfLE bot_le) (homOfLE le_top) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (n - 1) n (n + 1)).gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)

/-- Through `EInftyIsoCokernel`, the canonical map `opZ^n(⊥ ≤ q + 1, q + 1 ≤ ⊤) ⟶ E∞` is the
projection to the cokernel of `F_q H^n ⟶ F_{q+1} H^n`. -/
@[reassoc (attr := simp)]
lemma opcyclesToE_EInftyIsoCokernel_hom (q n : ℤ) :
    X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (coe_le_coe_add_one q))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le) (Subsingleton.elim _ _)
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫ (X.EInftyIsoCokernel q n).hom =
      cokernel.π (X.abutmentFiltrationMap q n) := by
  rw [EInftyIsoCokernel]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (X.shortComplexOpcyclesThreeδ₂Toδ₁_shortExact ..).gIsCokernel (colimit.isColimit _)
    WalkingParallelPair.one

/-- The `q`th filtration piece vanishes when `H^n(⊥ ≤ q)` does: the filtration is bounded below
in degree `n` when these vanish for small `q`. -/
lemma isZero_abutmentFiltration {q n : ℤ}
    (h : IsZero ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q))))) :
    IsZero (X.abutmentFiltration q n) :=
  have : Epi (X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (le_top : (q : EInt) ≤ ⊤)) n) := inferInstanceAs (Epi (cokernel.π _))
  IsZero.of_epi (X.pOpcycles _ _ n) h

/-- The `q`th filtration piece is the whole abutment when `H^n(q ≤ ⊤)` vanishes: the filtration
is exhaustive in degree `n` when these vanish for large `q`. -/
lemma isIso_abutmentFiltrationι {q n : ℤ}
    (h : IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : (q : EInt) ≤ ⊤))))) :
    IsIso (X.abutmentFiltrationι q n) := by
  have hepi : Epi ((X.H n).map (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (le_top : (q : EInt) ≤ ⊤)) (homOfLE bot_le) (Subsingleton.elim _ _))) :=
    (X.exact₂ _ _ _ (Subsingleton.elim _ _) n).epi_f (h.eq_of_tgt _ _)
  have : Epi (X.abutmentFiltrationι q n) :=
    @epi_of_epi_fac _ _ _ _ _ _ _ _ hepi (X.p_fromOpcycles _ _ _ (Subsingleton.elim _ _) n)
  exact isIso_of_mono_of_epi _

end CategoryTheory.Abelian.SpectralObject
