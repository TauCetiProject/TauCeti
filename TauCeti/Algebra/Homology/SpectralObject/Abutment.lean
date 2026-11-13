/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Stabilization

/-!
# The abutment of a spectral object indexed by `EInt` and its filtration

Let `X` be a spectral object in an abelian category, indexed by `EInt`. Its abutment in degree
`n` is `H^n(⊥ ≤ ⊤)` (`X.abutment n`), for a filtered complex the cohomology of the complex. It is
filtered by the images of the maps `H^n(⊥ ≤ q) ⟶ H^n(⊥ ≤ ⊤)`: the `q`th piece is
`opZ^n(⊥ ≤ q, q ≤ ⊤)`, the cokernel of `δ : H^{n-1}(q ≤ ⊤) ⟶ H^n(⊥ ≤ q)`, embedded in the abutment
by `X.abutmentFiltrationι q n` (a monomorphism, by exactness). The pieces increase with `q`
(`X.abutmentFiltrationMap q n`, monomorphisms compatible with the embeddings), and the limit object
`X.EInfty q n = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` of the spectral sequence is the graded piece: the cokernel
of `F_q H^n ⟶ F_{q+1} H^n` (`X.EInftyIsoCokernel`), from Mathlib's short exact sequence
`shortComplexOpcyclesThreeδ₂Toδ₁_shortExact`.

The filtration is bounded below and exhaustive in degree `n` as soon as `H^n(⊥ ≤ q)` vanishes for
small `q` (`isZero_abutmentFiltration`) and `H^n(q ≤ ⊤)` vanishes for large `q`
(`isIso_abutmentFiltrationι`). Vanishing graded pieces propagate both properties
(`isZero_abutmentFiltration_of_isZero_cokernel`, `isIso_abutmentFiltrationι_of_isZero_cokernel`),
so a finite filtration with a single nonzero graded piece has that piece as its abutment
(`cokernelAbutmentFiltrationMapIsoAbutment`).

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.abutment X n`: the object `H^n(⊥ ≤ ⊤)`.
* `CategoryTheory.Abelian.SpectralObject.abutmentFiltration X q n`: the `q`th filtration piece.
* `CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel X q n`: `E∞` is the graded piece
  (characterized by `opcyclesToE_EInftyIsoCokernel_hom`).
* `CategoryTheory.Abelian.SpectralObject.cokernelAbutmentFiltrationMapIsoAbutment`: the only
  nonzero graded piece of a finite filtration is the abutment.
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

/-- **Vanishing graded pieces keep the filtration at zero.** If the `a`th piece of the filtration of
the abutment in degree `n` vanishes, and so do the graded pieces `F_{j+1} H^n / F_j H^n` for
`a ≤ j < q`, then the `q`th piece vanishes. For `q ≤ a` this holds because the filtration
increases. -/
theorem isZero_abutmentFiltration_of_isZero_cokernel {a q n : ℤ}
    (ha : IsZero (X.abutmentFiltration a n))
    (h : ∀ j, a ≤ j → j < q → IsZero (cokernel (X.abutmentFiltrationMap j n))) :
    IsZero (X.abutmentFiltration q n) := by
  rcases le_or_gt q a with hqa | haq
  · clear h
    induction q, hqa using Int.leInductionDown with
    | base => exact ha
    | pred j hj ih =>
      have hj' : IsZero (X.abutmentFiltration (j - 1 + 1) n) := (sub_add_cancel j 1).symm ▸ ih
      exact IsZero.of_mono (X.abutmentFiltrationMap (j - 1) n) hj'
  suffices ∀ j, a ≤ j → j ≤ q → IsZero (X.abutmentFiltration j n) from this q haq.le le_rfl
  intro j hj
  induction j, hj using Int.leInduction with
  | base => exact fun _ ↦ ha
  | succ j hj ih =>
    intro hjq
    have : Epi (X.abutmentFiltrationMap j n) :=
      Abelian.epi_of_cokernel_π_eq_zero _ ((h j hj (by lia)).eq_of_tgt _ _)
    exact IsZero.of_epi (X.abutmentFiltrationMap j n) (ih (by lia))

/-- **Vanishing graded pieces keep the filtration exhaustive.** If the `b`th piece of the
filtration of the abutment in degree `n` is everything, and the graded pieces
`F_{j+1} H^n / F_j H^n` vanish for `q ≤ j < b`, then the `q`th piece is everything. For `b ≤ q`
this holds because the filtration increases. -/
theorem isIso_abutmentFiltrationι_of_isZero_cokernel {q b n : ℤ}
    (hb : IsIso (X.abutmentFiltrationι b n))
    (h : ∀ j, q ≤ j → j < b → IsZero (cokernel (X.abutmentFiltrationMap j n))) :
    IsIso (X.abutmentFiltrationι q n) := by
  rcases le_or_gt b q with hbq | hqb
  · clear h
    induction q, hbq using Int.leInduction with
    | base => exact hb
    | succ j hj ih =>
      have : Epi (X.abutmentFiltrationι (j + 1) n) :=
        epi_of_epi_fac (X.abutmentFiltrationMap_ι j n)
      exact isIso_of_mono_of_epi _
  suffices ∀ j, j ≤ b → q ≤ j → IsIso (X.abutmentFiltrationι j n) from this q hqb.le le_rfl
  intro j hj
  induction j, hj using Int.leInductionDown with
  | base => exact fun _ ↦ hb
  | pred j hj ih =>
    intro hqj
    have hj : IsIso (X.abutmentFiltrationι j n) := ih (by lia)
    have : Epi (X.abutmentFiltrationMap (j - 1) n) :=
      Abelian.epi_of_cokernel_π_eq_zero _ ((h (j - 1) hqj (by lia)).eq_of_tgt _ _)
    have : IsIso (X.abutmentFiltrationMap (j - 1) n) := isIso_of_mono_of_epi _
    have : IsIso (X.abutmentFiltrationι (j - 1 + 1) n) := (sub_add_cancel j 1).symm ▸ hj
    rw [← X.abutmentFiltrationMap_ι (j - 1) n]
    infer_instance

/-- If the filtration of the abutment in degree `n` vanishes at `a`, is everything at `b`, and
has no nonzero graded piece in `[a, b)` other than the `q`th one, then it has no nonzero graded
piece other than the `q`th one at all. -/
private theorem isZero_cokernel_abutmentFiltrationMap_of_ne {a b q n : ℤ}
    (ha : IsZero (X.abutmentFiltration a n)) (hb : IsIso (X.abutmentFiltrationι b n))
    (h : ∀ j, a ≤ j → j < b → j ≠ q → IsZero (cokernel (X.abutmentFiltrationMap j n)))
    {j : ℤ} (hjq : j ≠ q) : IsZero (cokernel (X.abutmentFiltrationMap j n)) := by
  by_cases haj : a ≤ j
  · by_cases hjb : j < b
    · exact h j haj hjb hjq
    have := X.isIso_abutmentFiltrationι_of_isZero_cokernel hb (q := j)
      fun _ _ _ ↦ (by lia : False).elim
    have := X.isIso_abutmentFiltrationι_of_isZero_cokernel hb (q := j + 1)
      fun _ _ _ ↦ (by lia : False).elim
    have : IsIso (X.abutmentFiltrationMap j n ≫ X.abutmentFiltrationι (j + 1) n) := by
      rw [abutmentFiltrationMap_ι]
      infer_instance
    have := IsIso.of_isIso_comp_right (X.abutmentFiltrationMap j n)
      (X.abutmentFiltrationι (j + 1) n)
    exact isZero_cokernel_of_epi _
  · have := (X.isZero_abutmentFiltration_of_isZero_cokernel ha (q := j + 1)
      fun _ _ _ ↦ (by lia : False).elim).epi (X.abutmentFiltrationMap j n)
    exact isZero_cokernel_of_epi _

/-- **A finite filtration with a single nonzero graded piece.** If the filtration of the abutment
in degree `n` vanishes at `a` and is everything at `b`, and its only graded piece between them that
may be nonzero is `F_{q+1} H^n / F_q H^n`, then that graded piece is the abutment `H^n(⊥ ≤ ⊤)`,
through the embedding of `F_{q+1} H^n`. -/
noncomputable def cokernelAbutmentFiltrationMapIsoAbutment {a b q n : ℤ}
    (ha : IsZero (X.abutmentFiltration a n)) (hb : IsIso (X.abutmentFiltrationι b n))
    (h : ∀ j, a ≤ j → j < b → j ≠ q → IsZero (cokernel (X.abutmentFiltrationMap j n))) :
    cokernel (X.abutmentFiltrationMap q n) ≅ X.abutment n :=
  have hq := X.isZero_abutmentFiltration_of_isZero_cokernel ha
    fun _ _ hjq ↦ X.isZero_cokernel_abutmentFiltrationMap_of_ne ha hb h hjq.ne
  have := X.isIso_abutmentFiltrationι_of_isZero_cokernel hb (q := q + 1)
    fun _ hj _ ↦ X.isZero_cokernel_abutmentFiltrationMap_of_ne ha hb h (by lia)
  cokernelIsoOfEq (hq.eq_of_src _ 0) ≪≫ cokernelZeroIsoTarget ≪≫
    asIso (X.abutmentFiltrationι (q + 1) n)

/-- `cokernelAbutmentFiltrationMapIsoAbutment` is induced by the embedding of `F_{q+1} H^n`. -/
@[reassoc (attr := simp)]
lemma π_cokernelAbutmentFiltrationMapIsoAbutment_hom {a b q n : ℤ}
    (ha : IsZero (X.abutmentFiltration a n)) (hb : IsIso (X.abutmentFiltrationι b n))
    (h : ∀ j, a ≤ j → j < b → j ≠ q → IsZero (cokernel (X.abutmentFiltrationMap j n))) :
    cokernel.π (X.abutmentFiltrationMap q n) ≫
        (X.cokernelAbutmentFiltrationMapIsoAbutment ha hb h).hom =
      X.abutmentFiltrationι (q + 1) n := by
  simp [cokernelAbutmentFiltrationMapIsoAbutment, cokernelZeroIsoTarget]

end CategoryTheory.Abelian.SpectralObject
