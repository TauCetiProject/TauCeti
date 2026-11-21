/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Basic
public import TauCeti.Algebra.Homology.SpectralObject.Stabilization

/-!
# The abutment of a spectral object indexed by `EInt` and its filtration

Let `X` be a spectral object in an abelian category, indexed by `EInt`. Its abutment in degree
`n` is `H^n(⊥ ≤ ⊤)` (`X.abutment n`), for a filtered complex the cohomology of the complex. It is
filtered by the images of the maps `H^n(⊥ ≤ q) ⟶ H^n(⊥ ≤ ⊤)`: the `q`th piece is
`opZ^n(⊥ ≤ q, q ≤ ⊤)`, the cokernel of `δ : H^{n-1}(q ≤ ⊤) ⟶ H^n(⊥ ≤ q)`, embedded in the abutment
by `X.abutmentFiltrationι q n` (a monomorphism, by exactness). The pieces increase with `q`
(`X.abutmentFiltrationMap q n`, compatible with the embeddings), and the limit object
`X.EInfty q n = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` of the spectral sequence is the graded piece: the cokernel
of `F_q H^n ⟶ F_{q+1} H^n` (`X.EInftyIsoCokernel`), from Mathlib's short exact sequence
`shortComplexOpcyclesThreeδ₂Toδ₁_shortExact`.

The filtration is bounded below and exhaustive in degree `n` as soon as `H^n(⊥ ≤ q)` vanishes for
small `q` (`isZero_abutmentFiltration`) and `H^n(q ≤ ⊤)` vanishes for large `q`
(`isIso_abutmentFiltrationι`). If `H^n(⊥ ≤ a)` and `H^n(b ≤ ⊤)` vanish for some `b ≤ a`, the
abutment itself vanishes (`isZero_abutment_of_le`); this is the case `⊥ ≤ b ≤ a ≤ ⊤` of
`isZero_H_obj_mk₁_of_isZero_of_isZero`, which holds for three composable morphisms in any index
category. If all graded pieces in degree `n` of a finite filtration vanish except one, that graded
piece is the whole abutment (`cokernelAbutmentFiltrationMapIsoAbutment`).

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.abutment X n`: the object `H^n(⊥ ≤ ⊤)`.
* `CategoryTheory.Abelian.SpectralObject.abutmentFiltration X q n`: the `q`th filtration piece.
* `CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel X q n`: `E∞` is the graded piece
  (characterized by `opcyclesToE_EInftyIsoCokernel_hom`).
* `CategoryTheory.Abelian.SpectralObject.cokernelAbutmentFiltrationMapIsoAbutment`: a graded piece
  is the whole abutment when the other graded pieces of a finite filtration vanish.
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

/-- The abutment in degree `n` vanishes when `H^n(⊥ ≤ a)` and `H^n(b ≤ ⊤)` vanish for some
`b ≤ a`: the filtration then starts above where it ends. -/
lemma isZero_abutment_of_le {a b n : ℤ} (hba : b ≤ a)
    (ha : IsZero ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a)))))
    (hb : IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : (b : EInt) ≤ ⊤))))) :
    IsZero (X.abutment n) :=
  X.isZero_H_obj_mk₁_of_isZero_of_isZero (homOfLE (bot_le : (⊥ : EInt) ≤ b))
    (homOfLE (WithBotTop.coe_le_coe.mpr hba)) (homOfLE (le_top : (a : EInt) ≤ ⊤)) _ _ _
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _) n ha hb

instance (q n : ℤ) : Mono (X.abutmentFiltrationMap q n) :=
  mono_of_mono_fac (X.abutmentFiltrationMap_ι q n)

/-- **A filtration concentrated in one graded piece.** Suppose that in degree `n` the piece
`F_a H^n` of the filtration of the abutment vanishes, the piece `F_b H^n` is the whole abutment, and
every graded piece `F_{q+1} H^n / F_q H^n` with `a ≤ q < b` vanishes except possibly the one at
`q₀`. Then `F_{q₀} H^n = 0` and `F_{q₀+1} H^n` is the whole abutment, so the graded piece at `q₀`
is the abutment. -/
noncomputable def cokernelAbutmentFiltrationMapIsoAbutment {n a b q₀ : ℤ} (ha : a ≤ q₀)
    (hb : q₀ < b) (hbot : IsZero (X.abutmentFiltration a n))
    (htop : IsIso (X.abutmentFiltrationι b n))
    (hgr : ∀ q, a ≤ q → q < b → q ≠ q₀ → IsZero (cokernel (X.abutmentFiltrationMap q n))) :
    cokernel (X.abutmentFiltrationMap q₀ n) ≅ X.abutment n :=
  -- Below `q₀` the pieces vanish, since each is a quotient of the previous one.
  have hzero : ∀ k : ℕ, ∀ q, q - a = k → q ≤ q₀ → IsZero (X.abutmentFiltration q n) := by
    intro k
    induction k with
    | zero =>
      intro q hq _
      obtain rfl : q = a := by lia
      exact hbot
    | succ k ih =>
      intro q hq hq₀
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by lia⟩
      have := Preadditive.epi_of_isZero_cokernel _ (hgr q (by lia) (by lia) (by lia))
      exact IsZero.of_epi (X.abutmentFiltrationMap q n) (ih q (by lia) (by lia))
  -- Above `q₀` the embeddings into the abutment are isomorphisms, since each piece is the next.
  have hiso : ∀ k : ℕ, ∀ q, b - q = k → q₀ < q → IsIso (X.abutmentFiltrationι q n) := by
    intro k
    induction k with
    | zero =>
      intro q hq _
      obtain rfl : q = b := by lia
      exact htop
    | succ k ih =>
      intro q hq hq₀
      have := Preadditive.epi_of_isZero_cokernel _ (hgr q (by lia) (by lia) (by lia))
      have := isIso_of_mono_of_epi (X.abutmentFiltrationMap q n)
      have := ih (q + 1) (by lia) (by lia)
      rw [← X.abutmentFiltrationMap_ι q n]
      infer_instance
  have := hiso (b - (q₀ + 1)).toNat (q₀ + 1) (by lia) (by lia)
  cokernelIsoOfEq ((hzero (q₀ - a).toNat q₀ (by lia) le_rfl).eq_of_src _ _) ≪≫
    cokernelZeroIsoTarget ≪≫ asIso (X.abutmentFiltrationι (q₀ + 1) n)

end CategoryTheory.Abelian.SpectralObject
