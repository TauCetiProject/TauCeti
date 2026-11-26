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
(`X.abutmentFiltrationMap q n`, a monomorphism compatible with the embeddings), and the limit object
`X.EInfty q n = E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` of the spectral sequence is the graded piece: the cokernel
of `F_q H^n ⟶ F_{q+1} H^n` (`X.EInftyIsoCokernel`), from Mathlib's short exact sequence
`shortComplexOpcyclesThreeδ₂Toδ₁_shortExact`.

The filtration is bounded below and exhaustive in degree `n` as soon as `H^n(⊥ ≤ q)` vanishes for
small `q` (`isZero_abutmentFiltration`) and `H^n(q ≤ ⊤)` vanishes for large `q`
(`isIso_abutmentFiltrationι`); more generally, the `q`th piece is the whole abutment as soon
as `H^n(⊥ ≤ q) ⟶ H^n(⊥ ≤ ⊤)` is an epimorphism (`isIso_abutmentFiltrationι_of_epi`). For
`a ≤ b`, the pieces are compared by `abutmentFiltrationMapOfLE`, a monomorphism which is an
isomorphism when the limit objects `X.EInfty s n` vanish for `a ≤ s < b`
(`isIso_abutmentFiltrationMapOfLE_of_isZero_EInfty`); in particular, if `F_b H^n` is the whole
abutment, so is `F_a H^n` (`isIso_abutmentFiltrationι_of_isZero_EInfty`). If `H^n(⊥ ≤ a)` and
`H^n(b ≤ ⊤)` vanish for some `b ≤ a`, the abutment itself vanishes
(`isZero_abutment_of_le`); this is the case `⊥ ≤ b ≤ a ≤ ⊤` of
`isZero_H_obj_mk₁_of_isZero_of_isZero`, which holds for three composable morphisms in any index
category.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.abutment X n`: the object `H^n(⊥ ≤ ⊤)`.
* `CategoryTheory.Abelian.SpectralObject.abutmentFiltration X q n`: the `q`th filtration piece.
* `CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel X q n`: `E∞` is the graded piece
  (characterized by `opcyclesToE_EInftyIsoCokernel_hom`).
* `CategoryTheory.Abelian.SpectralObject.abutmentFiltrationMapOfLE X a b n hab`: the comparison
  `F_a H^n ⟶ F_b H^n`, an isomorphism under the vanishing of the limit objects between `a` and
  `b` (`isIso_abutmentFiltrationMapOfLE_of_isZero_EInfty`).
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

/-- The inclusion of the `q`th piece of the filtration of the abutment into the `(q + 1)`st one is
a monomorphism, since both embed into the abutment compatibly. -/
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

/-- The `q`th filtration piece is the whole abutment when the map `H^n(⊥ ≤ q) ⟶ H^n(⊥ ≤ ⊤)` is
an epimorphism. -/
lemma isIso_abutmentFiltrationι_of_epi {q n : ℤ}
    [Epi ((X.H n).map (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (le_top : (q : EInt) ≤ ⊤)) (homOfLE bot_le) (Subsingleton.elim _ _)))] :
    IsIso (X.abutmentFiltrationι q n) := by
  have : Epi (X.abutmentFiltrationι q n) := epi_of_epi_fac (X.pOpcycles_abutmentFiltrationι q n)
  exact isIso_of_mono_of_epi _

/-- The `q`th filtration piece is the whole abutment when `H^n(q ≤ ⊤)` vanishes: the filtration
is exhaustive in degree `n` when these vanish for large `q`. -/
lemma isIso_abutmentFiltrationι {q n : ℤ}
    (h : IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : (q : EInt) ≤ ⊤))))) :
    IsIso (X.abutmentFiltrationι q n) :=
  have := X.epi_H_map_twoδ₂Toδ₁ n (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE le_top)
    (homOfLE bot_le) (Subsingleton.elim _ _) h
  X.isIso_abutmentFiltrationι_of_epi

/-- The comparison `F_a H^n ⟶ F_b H^n`, for `a ≤ b`, between two pieces of the filtration of the
abutment. -/
noncomputable def abutmentFiltrationMapOfLE (a b n : ℤ) (hab : a ≤ b) :
    X.abutmentFiltration a n ⟶ X.abutmentFiltration b n :=
  X.opcyclesMap _ _ _ _ (threeδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a))
    (homOfLE (WithBotTop.coe_le_coe.2 hab)) (homOfLE (le_top : (b : EInt) ≤ ⊤))
    (homOfLE bot_le) (homOfLE le_top) (Subsingleton.elim _ _) (Subsingleton.elim _ _)) n

/-- The comparison `X.abutmentFiltrationMapOfLE a b n` is compatible with the embeddings of the
pieces of the filtration into the abutment. -/
@[reassoc (attr := simp)]
lemma abutmentFiltrationMapOfLE_ι (a b n : ℤ) (hab : a ≤ b) :
    X.abutmentFiltrationMapOfLE a b n hab ≫ X.abutmentFiltrationι b n =
      X.abutmentFiltrationι a n := by
  rw [abutmentFiltrationMapOfLE, abutmentFiltrationι_eq, abutmentFiltrationι_eq,
    X.opcyclesMap_fromOpcycles _ _ _ _ _ _ _ _ _ (𝟙 _) n (by simp [threeδ₂Toδ₁])
    (by simp [threeδ₂Toδ₁]), CategoryTheory.Functor.map_id, Category.comp_id]

/-- The comparison between the pieces `F_a H^n` and `F_a H^n` is the identity. -/
@[simp]
lemma abutmentFiltrationMapOfLE_refl (a n : ℤ) :
    X.abutmentFiltrationMapOfLE a a n le_rfl = 𝟙 _ := by
  rw [← cancel_mono (X.abutmentFiltrationι a n), abutmentFiltrationMapOfLE_ι, Category.id_comp]

/-- The comparison `F_a H^n ⟶ F_b H^n` is a monomorphism, since both pieces embed into the
abutment compatibly. -/
instance (a b n : ℤ) (hab : a ≤ b) : Mono (X.abutmentFiltrationMapOfLE a b n hab) :=
  mono_of_mono_fac (X.abutmentFiltrationMapOfLE_ι a b n hab)

/-- The comparison between `F_a H^n` and `F_{a+1} H^n` is the inclusion
`X.abutmentFiltrationMap a n`. -/
lemma abutmentFiltrationMapOfLE_add_one (a n : ℤ) :
    X.abutmentFiltrationMapOfLE a (a + 1) n (by omega) = X.abutmentFiltrationMap a n := by
  rw [← cancel_mono (X.abutmentFiltrationι (a + 1) n), abutmentFiltrationMapOfLE_ι,
    abutmentFiltrationMap_ι]

/-- The comparisons between the pieces of the filtration compose: for `a ≤ b ≤ c`, the
comparison `F_a H^n ⟶ F_b H^n` followed by `F_b H^n ⟶ F_c H^n` is `F_a H^n ⟶ F_c H^n`. -/
@[reassoc (attr := simp)]
lemma abutmentFiltrationMapOfLE_trans (a b c n : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    X.abutmentFiltrationMapOfLE a b n hab ≫ X.abutmentFiltrationMapOfLE b c n hbc =
      X.abutmentFiltrationMapOfLE a c n (hab.trans hbc) := by
  rw [← cancel_mono (X.abutmentFiltrationι c n), Category.assoc, abutmentFiltrationMapOfLE_ι,
    abutmentFiltrationMapOfLE_ι, abutmentFiltrationMapOfLE_ι]

/-- The comparison `F_a H^n ⟶ F_b H^n` is the inclusion `F_a H^n ⟶ F_{a+1} H^n` followed by the
comparison `F_{a+1} H^n ⟶ F_b H^n`. -/
lemma abutmentFiltrationMap_comp_abutmentFiltrationMapOfLE (a b n : ℤ) (hab : a + 1 ≤ b) :
    X.abutmentFiltrationMap a n ≫ X.abutmentFiltrationMapOfLE (a + 1) b n hab =
      X.abutmentFiltrationMapOfLE a b n (by omega) := by
  rw [← cancel_mono (X.abutmentFiltrationι b n), Category.assoc, abutmentFiltrationMapOfLE_ι,
    abutmentFiltrationMap_ι, abutmentFiltrationMapOfLE_ι]

/-- If the limit objects `X.EInfty s n` vanish for `a ≤ s < b`, the pieces `F_a H^n` and
`F_b H^n` of the filtration of the abutment agree: the comparison `F_a H^n ⟶ F_b H^n` is an
isomorphism. -/
lemma isIso_abutmentFiltrationMapOfLE_of_isZero_EInfty {a b n : ℤ} (hab : a ≤ b)
    (h : ∀ s : ℤ, a ≤ s → s < b → IsZero (X.EInfty s n)) :
    IsIso (X.abutmentFiltrationMapOfLE a b n hab) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, b = a + m := ⟨(b - a).toNat, by omega⟩
  induction m generalizing a with
  | zero =>
    obtain rfl : b = a := by omega
    rw [abutmentFiltrationMapOfLE_refl]
    infer_instance
  | succ m ih =>
    have := ih (a := a + 1) (by omega) (fun s h₁ h₂ ↦ h s (by omega) h₂) (by omega)
    -- the inclusion `F_a H^n ⟶ F_{a+1} H^n` is a monomorphism with vanishing cokernel
    have : Epi (X.abutmentFiltrationMap a n) := Preadditive.epi_of_isZero_cokernel _
      ((h a le_rfl (by omega)).of_iso (X.EInftyIsoCokernel a n).symm)
    have : IsIso (X.abutmentFiltrationMap a n) := isIso_of_mono_of_epi _
    rw [← X.abutmentFiltrationMap_comp_abutmentFiltrationMapOfLE a b n (by omega)]
    infer_instance

/-- If the limit objects `X.EInfty s n` vanish for `a ≤ s < b` and `F_b H^n` is the whole
abutment, so is `F_a H^n`. -/
lemma isIso_abutmentFiltrationι_of_isZero_EInfty {a b n : ℤ} (hab : a ≤ b)
    (hb : IsIso (X.abutmentFiltrationι b n)) (h : ∀ s : ℤ, a ≤ s → s < b → IsZero (X.EInfty s n)) :
    IsIso (X.abutmentFiltrationι a n) := by
  have := X.isIso_abutmentFiltrationMapOfLE_of_isZero_EInfty hab h
  rw [← X.abutmentFiltrationMapOfLE_ι a b n hab]
  infer_instance

/-- The abutment in degree `n` vanishes when `H^n(⊥ ≤ a)` and `H^n(b ≤ ⊤)` vanish for some
`b ≤ a`: the filtration then starts above where it ends. -/
lemma isZero_abutment_of_le {a b n : ℤ} (hba : b ≤ a)
    (ha : IsZero ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a)))))
    (hb : IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : (b : EInt) ≤ ⊤))))) :
    IsZero (X.abutment n) :=
  X.isZero_H_obj_mk₁_of_isZero_of_isZero (homOfLE (bot_le : (⊥ : EInt) ≤ b))
    (homOfLE (WithBotTop.coe_le_coe.mpr hba)) (homOfLE (le_top : (a : EInt) ≤ ⊤)) _ _ _
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _) n ha hb

end CategoryTheory.Abelian.SpectralObject
