/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Borel` and its diagonal projection `TauCeti.GL2Borel.diag` define the two levels.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
-- The counts of units and unimodular rows of a finite local ring give the indices.
public import TauCeti.RingTheory.LocalRing.Card
-- `Ideal.Quotient.mk` and `QuotientGroup.rightRel` occur in the statements below.
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.GroupTheory.Coset.Defs
-- `MulAction.orbitRel.Quotient` and `SubMulAction` model the projective line.
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.GroupAction.Quotient
-- `IsDiscreteValuationRing` occurs in the statements of the specialization to `𝔭ᵉ`.
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
-- Non-public: `#(A ⧸ 𝔭ᵉ) = qᵉ` and the finiteness of `A ⧸ 𝔭ᵉ` are used only in the proofs for
-- `𝔭ᵉ`.
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.Quotient
-- Non-public, used only in the proofs: solving `v ᵥ* g⁻¹ = w`, lifting units modulo a proper
-- ideal of a local ring, the quotient as a local ring and its residue field, and the properness of
-- `𝔭ᵉ`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
import TauCeti.RingTheory.LocalRing.Quotient
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient
import TauCeti.RingTheory.LocalRing.Basic

/-!
# The congruence levels `K₀(I)` and `K₁(I)` of `GL₂`

Let `A` be a commutative ring and `I` an ideal of `A`. The **congruence levels** of `GL₂(A)` are

* `K₀(I) = {(a b; c d) ∈ GL₂(A) : c ∈ I}`, the preimage under reduction modulo `I` of the Borel
  subgroup `TauCeti.GL2Borel` of `GL₂(A ⧸ I)`, and
* `K₁(I) = {γ ∈ K₀(I) : d - 1 ∈ I}`, the kernel of the lower-right character
  `TauCeti.GL2K0.lowerRight : K₀(I) →* (A ⧸ I)ˣ`, which is the second diagonal entry of the
  reduction modulo `I`.

When `A` is the valuation ring of a nonarchimedean local field and `I = 𝔭ᵉ`, these are the levels
at which newforms and Hecke operators for `GL₂` are defined, and `K₀(𝔭ᵉ)` is the unit group of
the standard Eichler order of level `𝔭ᵉ`.

Both levels are read off from the **bottom row modulo `I`** (`TauCeti.bottomRowMod`). The bottom
row of an invertible matrix is unimodular, and the bottom row of `γ' γ⁻¹` is the bottom row of
`γ'` times `γ⁻¹`. So, over every commutative ring, `γ` and `γ'` lie in one right coset of `K₁(I)`
exactly when their bottom rows agree modulo `I`, and in one right coset of `K₀(I)` exactly when
they agree up to a unit of `A ⧸ I`. Over a local ring every unimodular row of `(A ⧸ I)²` is a
bottom row, since it has a unit coordinate that lifts to a unit of `A`. This identifies

* `K₁(I)\GL₂(A)` with the unimodular rows of `(A ⧸ I)²` (`TauCeti.GL2K1.rightCosetEquiv`), and
* `K₀(I)\GL₂(A)` with the projective line `ℙ¹(A ⧸ I)`, the unimodular rows modulo `(A ⧸ I)ˣ`
  (`TauCeti.GL2K0.rightCosetEquiv`), modelled as the orbits of `(A ⧸ I)ˣ` on
  `TauCeti.Module.unimodularSubMulAction`.

Counting unimodular rows and units of the local ring `A ⧸ I` then gives the indices. With `q` the
size of the residue field of `A`, `I ≠ A` and `A ⧸ I` finite,

* `q² · [GL₂(A) : K₁(I)] = #(A ⧸ I)² · (q² - 1)`,
* `q · [GL₂(A) : K₀(I)] = #(A ⧸ I) · (q + 1)`, and
* `q · [K₀(I) : K₁(I)] = #(A ⧸ I) · (q - 1)`, the number of units of `A ⧸ I`.

For a discrete valuation ring with finite residue field and `e ≥ 1`, where `#(A ⧸ 𝔭ᵉ) = qᵉ`,
these read
`[GL₂(A) : K₀(𝔭ᵉ)] = qᵉ⁻¹ (q + 1)`, `[GL₂(A) : K₁(𝔭ᵉ)] = q²ᵉ⁻² (q² - 1)` and
`[K₀(𝔭ᵉ) : K₁(𝔭ᵉ)] = qᵉ⁻¹ (q - 1)`.

The projective line of `A ⧸ I` is not the projective line of a field with `#(A ⧸ I)` elements:
`ℙ¹(ℤ/4)` has six points, the four `(1 : t)` together with `(0 : 1)` and `(2 : 1)`, and the
formula for `K₀` gives `[GL₂(ℤ₂) : K₀(4)] = 6`, not five.

## Main definitions

* `TauCeti.GL2K0 I`, `TauCeti.GL2K1 I`: the congruence levels of `GL₂(A)`.
* `TauCeti.GL2K0.lowerRight`: the lower-right entry modulo `I`, a character of `K₀(I)` with kernel
  `K₁(I)`.
* `TauCeti.bottomRowMod I γ`: the bottom row of `γ` modulo `I`.

## Main results

* `TauCeti.GL2K0.mem_iff`, `TauCeti.GL2K1.mem_iff`: the entry conditions.
* `TauCeti.GL2K0_mono`, `TauCeti.GL2K1_mono`: the levels are monotone in `I`.
* `TauCeti.GL2K1.ker_map_le`: the kernel of reduction modulo `I` lies in `K₁(I)`.
* `TauCeti.GL2K1.rightRel_iff`, `TauCeti.GL2K0.rightRel_iff`: right cosets are determined by the
  bottom row modulo `I`, exactly or up to a unit, over every commutative ring.
* `TauCeti.GL2K1.rightCosetEquiv`, `TauCeti.GL2K0.rightCosetEquiv`: over a local ring, the right
  cosets are the unimodular rows of `(A ⧸ I)²` and the points of `ℙ¹(A ⧸ I)`.
* `TauCeti.GL2K1.card_residueField_sq_mul_index`, `TauCeti.GL2K0.card_residueField_mul_index`,
  `TauCeti.GL2K1.card_residueField_mul_relIndex`: the three indices over a local ring.
* `TauCeti.GL2K0.index_maximalIdeal_pow`, `TauCeti.GL2K1.index_maximalIdeal_pow`,
  `TauCeti.GL2K1.relIndex_maximalIdeal_pow`: the indices at `𝔭ᵉ` over a discrete valuation ring.

## References

* J. Voight, *Quaternion Algebras*, GTM 288, Lemma 26.4.1 and 26.4.3 (pp. 438–440), for the
  projective line of a commutative ring and `#ℙ¹(O_v ⧸ 𝔭_v^e) = q_v^e + q_v^{e-1}`.
-/

public section

namespace TauCeti

open Matrix

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The congruence level `K₀(I)` of `GL₂(A)`: the matrices whose lower-left entry lies in `I`,
that is, the preimage of the Borel subgroup of `GL₂(A ⧸ I)` under reduction modulo `I`. -/
def GL2K0 : Subgroup (GL (Fin 2) A) :=
  (GL2Borel (A ⧸ I)).comap (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I))

namespace GL2K0

variable {I}

/-- `g ∈ K₀(I)` exactly when its lower-left entry lies in `I`. -/
@[simp]
theorem mem_iff {g : GL (Fin 2) A} :
    g ∈ GL2K0 I ↔ (g : Matrix (Fin 2) (Fin 2) A) 1 0 ∈ I := by
  rw [GL2K0, Subgroup.mem_comap, GL2Borel.mem_iff, Matrix.GeneralLinearGroup.map_apply,
    Ideal.Quotient.eq_zero_iff_mem]

variable (I)

/-- The **lower-right character** of `K₀(I)`: the lower-right entry modulo `I`, which is a unit
of `A ⧸ I`. It is the second diagonal entry of the reduction modulo `I`, an element of the Borel
subgroup of `GL₂(A ⧸ I)`. -/
def lowerRight : GL2K0 I →* (A ⧸ I)ˣ :=
  (MonoidHom.snd _ _).comp <| GL2Borel.diag.comp <|
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).subgroupComap (GL2Borel (A ⧸ I))

@[simp]
theorem val_lowerRight (g : GL2K0 I) :
    ((lowerRight I g : (A ⧸ I)ˣ) : A ⧸ I) =
      Ideal.Quotient.mk I (((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1) := by
  -- `lowerRight` is the composite of `diag` with the restriction of the reduction map to
  -- `GL2K0 I`, which is the comap defining `GL2K0 I`.
  exact (GL2Borel.diag_snd_val _).trans (Matrix.GeneralLinearGroup.map_apply _ _ _ _)

end GL2K0

/-- The congruence level `K₁(I)` of `GL₂(A)`: the matrices whose lower-left entry lies in `I`
and whose lower-right entry is `1` modulo `I`, that is, the kernel of the lower-right character of
`K₀(I)`. -/
def GL2K1 : Subgroup (GL (Fin 2) A) :=
  (GL2K0.lowerRight I).ker.map (GL2K0 I).subtype

namespace GL2K1

variable {I}

/-- `g ∈ K₁(I)` exactly when its lower-left entry lies in `I` and its lower-right entry is `1`
modulo `I`. -/
@[simp]
theorem mem_iff {g : GL (Fin 2) A} :
    g ∈ GL2K1 I ↔ (g : Matrix (Fin 2) (Fin 2) A) 1 0 ∈ I ∧
      (g : Matrix (Fin 2) (Fin 2) A) 1 1 - 1 ∈ I := by
  rw [← GL2K0.mem_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.property, ?_⟩
    rw [Subgroup.coe_subtype, ← Ideal.Quotient.eq, ← GL2K0.val_lowerRight,
      MonoidHom.mem_ker.mp hg, Units.val_one, map_one]
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr (Units.ext ?_), rfl⟩
    rw [GL2K0.val_lowerRight, Units.val_one, ← map_one (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq.mpr h

variable (I)

theorem le_GL2K0 : GL2K1 I ≤ GL2K0 I :=
  Subgroup.map_subtype_le _

/-- Inside `K₀(I)`, the level `K₁(I)` is the kernel of the lower-right character. -/
theorem subgroupOf_GL2K0 : (GL2K1 I).subgroupOf (GL2K0 I) = (GL2K0.lowerRight I).ker :=
  Subgroup.comap_map_eq_self_of_injective (GL2K0 I).subtype_injective _

instance normal_subgroupOf_GL2K0 : ((GL2K1 I).subgroupOf (GL2K0 I)).Normal := by
  rw [subgroupOf_GL2K0]
  infer_instance

/-- The index of `K₁(I)` in `K₀(I)` is the number of values of the lower-right character. -/
theorem relIndex_GL2K0 :
    (GL2K1 I).relIndex (GL2K0 I) = Nat.card (GL2K0.lowerRight I).range := by
  rw [Subgroup.relIndex, subgroupOf_GL2K0, Subgroup.index_ker]

end GL2K1

/-! ### Monotonicity and the kernel of reduction -/

/-- `K₀` is monotone in the ideal. -/
theorem GL2K0_mono : Monotone (GL2K0 (A := A)) :=
  fun _ _ hIJ _ hg ↦ GL2K0.mem_iff.mpr (hIJ (GL2K0.mem_iff.mp hg))

/-- `K₁` is monotone in the ideal. -/
theorem GL2K1_mono : Monotone (GL2K1 (A := A)) := fun _ _ hIJ _ hg ↦
  GL2K1.mem_iff.mpr ⟨hIJ (GL2K1.mem_iff.mp hg).1, hIJ (GL2K1.mem_iff.mp hg).2⟩

/-- `K₀` of the unit ideal is all of `GL₂(A)`. -/
@[simp]
theorem GL2K0_top : GL2K0 (⊤ : Ideal A) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ GL2K0.mem_iff.mpr Submodule.mem_top

/-- `K₁` of the unit ideal is all of `GL₂(A)`. -/
@[simp]
theorem GL2K1_top : GL2K1 (⊤ : Ideal A) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ GL2K1.mem_iff.mpr ⟨Submodule.mem_top, Submodule.mem_top⟩

/-- The kernel of reduction modulo `I` is contained in `K₁(I)`. -/
theorem GL2K1.ker_map_le :
    (Matrix.GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker ≤ GL2K1 I := by
  intro g hg
  rw [Matrix.GeneralLinearGroup.mem_ker_map_quotientMk_iff] at hg
  simpa using And.intro (hg 1 0) (hg 1 1)

/-! ### The bottom row modulo `I` -/

/-- The bottom row of `g ∈ GL₂(A)`, reduced modulo `I`. It determines the right coset of `g`
modulo `K₁(I)`. -/
def bottomRowMod (g : GL (Fin 2) A) : Fin 2 → A ⧸ I :=
  fun j ↦ Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) A) 1 j)

@[simp]
theorem bottomRowMod_apply (g : GL (Fin 2) A) (j : Fin 2) :
    bottomRowMod I g j = Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) A) 1 j) :=
  (rfl)

/-- The bottom row modulo `I` is the bottom row of the reduction modulo `I`. -/
theorem bottomRowMod_eq (g : GL (Fin 2) A) :
    bottomRowMod I g =
      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g : GL (Fin 2) (A ⧸ I)) :
        Matrix (Fin 2) (Fin 2) (A ⧸ I)) 1 := by
  ext j
  rw [bottomRowMod_apply, Matrix.GeneralLinearGroup.map_apply]

/-- The bottom row of a product is the bottom row of the first factor times the second factor. -/
theorem bottomRowMod_mul (g h : GL (Fin 2) A) :
    bottomRowMod I (g * h) = bottomRowMod I g ᵥ*
      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) h : GL (Fin 2) (A ⧸ I)) :
        Matrix (Fin 2) (Fin 2) (A ⧸ I)) := by
  ext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- The bottom row of an invertible matrix is unimodular modulo every ideal. -/
theorem isUnimodular_bottomRowMod (g : GL (Fin 2) A) :
    Module.IsUnimodular (A ⧸ I) (bottomRowMod I g) := by
  rw [bottomRowMod_eq]
  exact Matrix.isUnimodular_apply_of_isUnit_det
    (Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g)) 1

/-- The bottom row of `g` modulo `I` is the unit row `(0, 1)` times the reduction of `g`. -/
private theorem single_one_vecMul_map (g : GL (Fin 2) A) :
    Pi.single 1 1 ᵥ* ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g :
      GL (Fin 2) (A ⧸ I)) : Matrix (Fin 2) (Fin 2) (A ⧸ I)) = bottomRowMod I g := by
  ext j
  rw [Matrix.single_one_vecMul, Matrix.row_apply, bottomRowMod_eq]

namespace GL2K1

variable {I}

/-- An element lies in `K₁(I)` exactly when its bottom row is `(0, 1)` modulo `I`. -/
theorem mem_iff_bottomRowMod {g : GL (Fin 2) A} :
    g ∈ GL2K1 I ↔ bottomRowMod I g = Pi.single 1 1 := by
  simp [funext_iff, Fin.forall_fin_two, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.Quotient.eq]

/-- **Right cosets of `K₁(I)`**: over every commutative ring, `g` and `g'` lie in one right coset
`K₁(I) g` exactly when their bottom rows agree modulo `I`. -/
theorem rightRel_iff {g g' : GL (Fin 2) A} :
    QuotientGroup.rightRel (GL2K1 I) g g' ↔ bottomRowMod I g = bottomRowMod I g' := by
  rw [QuotientGroup.rightRel_apply, mem_iff_bottomRowMod, bottomRowMod_mul, map_inv,
    Matrix.GeneralLinearGroup.vecMul_eq_iff_eq_vecMul_inv, inv_inv, single_one_vecMul_map, eq_comm]

end GL2K1

namespace GL2K0

variable {I}

/-- An element lies in `K₀(I)` exactly when its bottom row is a unit multiple of `(0, 1)`
modulo `I`. -/
theorem mem_iff_bottomRowMod {g : GL (Fin 2) A} :
    g ∈ GL2K0 I ↔ ∃ u : (A ⧸ I)ˣ, bottomRowMod I g = u • Pi.single 1 1 := by
  constructor
  · intro hg
    refine ⟨lowerRight I ⟨g, hg⟩, funext fun j ↦ ?_⟩
    fin_cases j
    · simpa [Ideal.Quotient.eq_zero_iff_mem] using mem_iff.mp hg
    · simp [Units.smul_def]
  · rintro ⟨u, hu⟩
    have h0 := congrFun hu 0
    rw [bottomRowMod_apply, Pi.smul_apply, Pi.single_eq_of_ne (by decide), smul_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h0
    exact mem_iff.mpr h0

/-- **Right cosets of `K₀(I)`**: over every commutative ring, `g` and `g'` lie in one right coset
`K₀(I) g` exactly when their bottom rows agree modulo `I` up to a unit of `A ⧸ I`. -/
theorem rightRel_iff {g g' : GL (Fin 2) A} :
    QuotientGroup.rightRel (GL2K0 I) g g' ↔
      ∃ u : (A ⧸ I)ˣ, u • bottomRowMod I g = bottomRowMod I g' := by
  rw [QuotientGroup.rightRel_apply, mem_iff_bottomRowMod]
  refine exists_congr fun u ↦ ?_
  rw [bottomRowMod_mul, map_inv, Matrix.GeneralLinearGroup.vecMul_eq_iff_eq_vecMul_inv, inv_inv,
    Units.smul_def, Matrix.smul_vecMul, single_one_vecMul_map, ← Units.smul_def, eq_comm]

end GL2K0

/-! ### The image of the lower-right character -/

/-- The lower-right character of `K₀(I)` is surjective over every commutative ring: for lifts `a`
of `w⁻¹` and `d` of `w`, the matrix `(a 1; ad - 1 d)` has determinant `1`, lies in `K₀(I)` and has
lower-right entry `d`. -/
theorem GL2K0.lowerRight_surjective : Function.Surjective (GL2K0.lowerRight I) := by
  intro w
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((w⁻¹ : (A ⧸ I)ˣ) : A ⧸ I)
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (w : A ⧸ I)
  have hc : a * d - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_mul, ha, hd, map_one, Units.inv_mul]
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' !![a, 1; a * d - 1, d] (by simp),
    GL2K0.mem_iff.mpr (by simpa using hc)⟩, Units.ext ?_⟩
  simp [hd]

/-- **The index of `K₁(I)` in `K₀(I)`** is the number of units of `A ⧸ I`. -/
theorem GL2K1.relIndex_GL2K0_eq_card_units :
    (GL2K1 I).relIndex (GL2K0 I) = Nat.card (A ⧸ I)ˣ := by
  rw [GL2K1.relIndex_GL2K0, MonoidHom.range_eq_top_of_surjective _
    (GL2K0.lowerRight_surjective I), Subgroup.card_top]

/-! ### Lifting over a local ring -/

section IsLocalRing

variable [IsLocalRing A]

/-- **Every unimodular row is a bottom row**: over a local ring `A`, every unimodular row of
`(A ⧸ I)²` is the bottom row modulo `I` of an element of `GL₂(A)`. One of its coordinates is a unit
of `A ⧸ I`, which lifts to a unit of `A`, and `(x, y)` is the bottom row of `(1 0; x y)` when `y` is
a unit and of `(0 -1; x y)` when `x` is. -/
theorem exists_bottomRowMod_eq {v : Fin 2 → A ⧸ I} (hv : Module.IsUnimodular (A ⧸ I) v) :
    ∃ g : GL (Fin 2) A, bottomRowMod I g = v := by
  by_cases hI : I = ⊤
  · have : Subsingleton (A ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI
    exact ⟨1, Subsingleton.elim _ _⟩
  have : IsLocalRing (A ⧸ I) := isLocalRing_quotient hI
  obtain ⟨i, hi⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp hv
  obtain ⟨u, hu⟩ := Ideal.unitsMap_quotientMk_surjective_of_ne_top hI hi.unit
  have hu' : Ideal.Quotient.mk I (u : A) = v i := congrArg Units.val hu
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (v 0)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (v 1)
  fin_cases i
  · refine ⟨Matrix.GeneralLinearGroup.mk'' !![0, -1; (u : A), y] (by simp), ?_⟩
    ext j
    fin_cases j <;> simp [hu', hy]
  · refine ⟨Matrix.GeneralLinearGroup.mk'' !![1, 0; x, (u : A)] (by simp), ?_⟩
    ext j
    fin_cases j <;> simp [hu', hx]

/-- **`K₁(I)\GL₂(A)` is the set of unimodular rows of `(A ⧸ I)²`**: over a local ring `A`, the
bottom row modulo `I` identifies the right cosets of `K₁(I)` with the unimodular rows. -/
noncomputable def GL2K1.rightCosetEquiv :
    Quotient (QuotientGroup.rightRel (GL2K1 I)) ≃
      {v : Fin 2 → A ⧸ I // Module.IsUnimodular (A ⧸ I) v} :=
  Equiv.ofBijective
    (Quotient.lift (fun g ↦ ⟨bottomRowMod I g, isUnimodular_bottomRowMod I g⟩)
      fun _ _ h ↦ Subtype.ext (GL2K1.rightRel_iff.mp h))
    ⟨by
      rintro ⟨g⟩ ⟨g'⟩ h
      exact Quotient.sound (GL2K1.rightRel_iff.mpr (congrArg Subtype.val h)),
    fun v ↦
      let ⟨g, hg⟩ := exists_bottomRowMod_eq I v.property
      ⟨Quotient.mk _ g, Subtype.ext hg⟩⟩

@[simp]
theorem GL2K1.rightCosetEquiv_mk (g : GL (Fin 2) A) :
    ((GL2K1.rightCosetEquiv I (Quotient.mk _ g) : Fin 2 → A ⧸ I)) = bottomRowMod I g :=
  (rfl)

/-- **`K₀(I)\GL₂(A)` is the projective line `ℙ¹(A ⧸ I)`**: over a local ring `A`, the bottom row
modulo `I` identifies the right cosets of `K₀(I)` with the unimodular rows of `(A ⧸ I)²` up to a
unit of `A ⧸ I`. -/
noncomputable def GL2K0.rightCosetEquiv :
    Quotient (QuotientGroup.rightRel (GL2K0 I)) ≃
      MulAction.orbitRel.Quotient (A ⧸ I)ˣ
        (TauCeti.Module.unimodularSubMulAction (A ⧸ I) (Fin 2 → A ⧸ I)) :=
  Equiv.ofBijective
    (Quotient.map (fun g ↦ ⟨bottomRowMod I g,
        TauCeti.Module.mem_unimodularSubMulAction.mpr (isUnimodular_bottomRowMod I g)⟩)
      fun _ _ h ↦ by
        obtain ⟨u, hu⟩ := GL2K0.rightRel_iff.mp h
        exact MulAction.orbitRel_apply.mpr ⟨u⁻¹, Subtype.ext (by simp [← hu])⟩)
    ⟨by
      rintro ⟨g⟩ ⟨g'⟩ h
      obtain ⟨u, hu⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
      have hu' : u • bottomRowMod I g' = bottomRowMod I g := congrArg Subtype.val hu
      exact Quotient.sound (GL2K0.rightRel_iff.mpr ⟨u⁻¹, by rw [← hu', inv_smul_smul]⟩),
    by
      rintro ⟨v⟩
      obtain ⟨g, hg⟩ :=
        exists_bottomRowMod_eq I (TauCeti.Module.mem_unimodularSubMulAction.mp v.property)
      exact ⟨Quotient.mk _ g, congrArg (Quotient.mk _) (Subtype.ext hg)⟩⟩

@[simp]
theorem GL2K0.rightCosetEquiv_mk (g : GL (Fin 2) A) :
    GL2K0.rightCosetEquiv I (Quotient.mk _ g) =
      Quotient.mk _ ⟨bottomRowMod I g,
        TauCeti.Module.mem_unimodularSubMulAction.mpr (isUnimodular_bottomRowMod I g)⟩ :=
  (rfl)

/-- Over a local ring, the index of `K₁(I)` is the number of unimodular rows of `(A ⧸ I)²`. -/
theorem GL2K1.index_eq_card :
    (GL2K1 I).index = Nat.card {v : Fin 2 → A ⧸ I // Module.IsUnimodular (A ⧸ I) v} := by
  rw [Subgroup.index_eq_card,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _),
    Nat.card_congr (GL2K1.rightCosetEquiv I)]

/-- Over a local ring, the index of `K₀(I)` is the number of points of the projective line
`ℙ¹(A ⧸ I)`. -/
theorem GL2K0.index_eq_card :
    (GL2K0 I).index = Nat.card (MulAction.orbitRel.Quotient (A ⧸ I)ˣ
      (TauCeti.Module.unimodularSubMulAction (A ⧸ I) (Fin 2 → A ⧸ I))) := by
  rw [Subgroup.index_eq_card,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _),
    Nat.card_congr (GL2K0.rightCosetEquiv I)]

/-! ### The indices over a local ring with finite quotient -/

open _root_.IsLocalRing

variable [Finite (A ⧸ I)] {I}

/-- **The index of `K₁(I)`** over a local ring with finite quotient `A ⧸ I ≠ 0`:
`q² · [GL₂(A) : K₁(I)] = #(A ⧸ I)² · (q² - 1)`, where `q` is the size of the residue field. -/
theorem GL2K1.card_residueField_sq_mul_index (hI : I ≠ ⊤) :
    Nat.card (ResidueField A) ^ 2 * (GL2K1 I).index =
      Nat.card (A ⧸ I) ^ 2 * (Nat.card (ResidueField A) ^ 2 - 1) := by
  have := isLocalRing_quotient hI
  have hq := card_residueField_of_surjective (Ideal.Quotient.mk_surjective (I := I))
  simpa [← hq, GL2K1.index_eq_card] using
    TauCeti.IsLocalRing.card_residueField_pow_mul_card_isUnimodular (A ⧸ I) (Fin 2)

/-- **The index of `K₁(I)` in `K₀(I)`** over a local ring with finite quotient `A ⧸ I ≠ 0`:
`q · [K₀(I) : K₁(I)] = #(A ⧸ I) · (q - 1)`, the number of units of `A ⧸ I` multiplied by `q`. -/
theorem GL2K1.card_residueField_mul_relIndex (hI : I ≠ ⊤) :
    Nat.card (ResidueField A) * (GL2K1 I).relIndex (GL2K0 I) =
      Nat.card (A ⧸ I) * (Nat.card (ResidueField A) - 1) := by
  have := isLocalRing_quotient hI
  have hq := card_residueField_of_surjective (Ideal.Quotient.mk_surjective (I := I))
  rw [GL2K1.relIndex_GL2K0_eq_card_units, ← hq]
  exact TauCeti.IsLocalRing.card_residueField_mul_card_units (A ⧸ I)

/-- **The index of `K₀(I)`** over a local ring with finite quotient `A ⧸ I ≠ 0`:
`q · [GL₂(A) : K₀(I)] = #(A ⧸ I) · (q + 1)`, where `q` is the size of the residue field. -/
theorem GL2K0.card_residueField_mul_index (hI : I ≠ ⊤) :
    Nat.card (ResidueField A) * (GL2K0 I).index =
      Nat.card (A ⧸ I) * (Nat.card (ResidueField A) + 1) := by
  have := isLocalRing_quotient hI
  have hq := card_residueField_of_surjective (Ideal.Quotient.mk_surjective (I := I))
  have : Finite (ResidueField (A ⧸ I)) := Finite.of_surjective _ residue_surjective
  have hq2 : 2 ≤ Nat.card (ResidueField A) := hq ▸ Finite.one_lt_card
  have hR : 0 < Nat.card (A ⧸ I) := Nat.card_pos
  have h1 := GL2K1.card_residueField_sq_mul_index hI
  have h2 := GL2K1.card_residueField_mul_relIndex hI
  rw [← Subgroup.relIndex_mul_index (GL2K1.le_GL2K0 I)] at h1
  set q := Nat.card (ResidueField A)
  -- Multiply the claim by `#(A ⧸ I) · (q - 1) = q · [K₀(I) : K₁(I)]` and compare with `h1`.
  refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hR (by omega) : 0 < Nat.card (A ⧸ I) * (q - 1)) ?_
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
  calc q * (GL2K0 I).index * (Nat.card (A ⧸ I) * (q - 1))
      = q ^ 2 * ((GL2K1 I).relIndex (GL2K0 I) * (GL2K0 I).index) := by rw [← h2]; ring
    _ = Nat.card (A ⧸ I) * (q + 1) * (Nat.card (A ⧸ I) * (q - 1)) := by rw [h1, hsq]; ring

end IsLocalRing

/-! ### The levels `K₀(𝔭ᵉ)` and `K₁(𝔭ᵉ)` of a discrete valuation ring -/

section IsDiscreteValuationRing

open _root_.IsLocalRing

variable [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] {e : ℕ}

/-- Cancelling `q > 0` from `q · x = qᵉ · c` with `e ≥ 1`: the step shared by the three indices at
`𝔭ᵉ`, where `#(A ⧸ 𝔭ᵉ) = qᵉ`. -/
private theorem eq_pow_sub_one_mul_of_mul_eq {q x c : ℕ} (hq : 0 < q) (he : e ≠ 0)
    (h : q * x = q ^ e * c) : x = q ^ (e - 1) * c := by
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [h, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]

/-- **`[GL₂(A) : K₀(𝔭ᵉ)] = qᵉ⁻¹ (q + 1)`** for a discrete valuation ring with finite residue field
of size `q` and `e ≥ 1`. -/
theorem GL2K0.index_maximalIdeal_pow (he : e ≠ 0) :
    (GL2K0 (maximalIdeal A ^ e)).index =
      Nat.card (ResidueField A) ^ (e - 1) * (Nat.card (ResidueField A) + 1) := by
  have h := GL2K0.card_residueField_mul_index (IsLocalRing.maximalIdeal_pow_ne_top (R := A) he)
  rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow] at h
  exact eq_pow_sub_one_mul_of_mul_eq Nat.card_pos he h

/-- **`[GL₂(A) : K₁(𝔭ᵉ)] = q²ᵉ⁻² (q² - 1)`** for a discrete valuation ring with finite residue
field of size `q` and `e ≥ 1`. -/
theorem GL2K1.index_maximalIdeal_pow (he : e ≠ 0) :
    (GL2K1 (maximalIdeal A ^ e)).index =
      Nat.card (ResidueField A) ^ (2 * e - 2) * (Nat.card (ResidueField A) ^ 2 - 1) := by
  have h := GL2K1.card_residueField_sq_mul_index (IsLocalRing.maximalIdeal_pow_ne_top (R := A) he)
  rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, ← pow_mul, mul_comm e,
    pow_mul] at h
  rw [show 2 * e - 2 = 2 * (e - 1) by omega, pow_mul]
  exact eq_pow_sub_one_mul_of_mul_eq (pow_pos Nat.card_pos 2) he h

/-- **`[K₀(𝔭ᵉ) : K₁(𝔭ᵉ)] = qᵉ⁻¹ (q - 1)`**, the number of units of `A ⧸ 𝔭ᵉ`, for a discrete
valuation ring with finite residue field of size `q` and `e ≥ 1`. -/
theorem GL2K1.relIndex_maximalIdeal_pow (he : e ≠ 0) :
    (GL2K1 (maximalIdeal A ^ e)).relIndex (GL2K0 (maximalIdeal A ^ e)) =
      Nat.card (ResidueField A) ^ (e - 1) * (Nat.card (ResidueField A) - 1) := by
  have h := GL2K1.card_residueField_mul_relIndex (IsLocalRing.maximalIdeal_pow_ne_top (R := A) he)
  rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow] at h
  exact eq_pow_sub_one_mul_of_mul_eq Nat.card_pos he h

end IsDiscreteValuationRing

end TauCeti
