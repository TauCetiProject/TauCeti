/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2K0`, `TauCeti.bottomRowMod` and the lifting of unimodular rows over a local ring.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
-- `GL₂(A)` acts on `A²` through `Matrix.mulVec`, and so on its submodules.
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.Algebra.Module.Submodule.Pointwise
-- `Subalgebra`, `Submonoid.units` and quotient modules occur in the statements below.
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.LinearAlgebra.Quotient.Basic
-- Non-public: the coordinate criterion for unimodular rows, used only in the proofs.
import TauCeti.LinearAlgebra.Unimodular
import TauCeti.Algebra.Module.Submodule.Pointwise
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The standard order `O₀(I)` and the lattices of `K₀(I)`

Let `A` be a commutative ring and `I` an ideal of `A`. The **standard order of level `I`** is the
subalgebra

```text
O₀(I) = {(a b; c d) ∈ M₂(A) : c ∈ I}
```

of `M₂(A)` (`TauCeti.M2O0`). When `A` is the valuation ring of a nonarchimedean local field and
`I = 𝔭ᵉ`, it is the local form of an Eichler order of level `𝔭ᵉ`. Its unit group is the
congruence level `K₀(I)` of `TauCeti.GL2K0`, and as an additive group it has index `#(A ⧸ I)` in
`M₂(A)`, the lower-left entry modulo `I` being the only condition.

The level `K₀(I)` is also the stabilizer in `GL₂(A)` of the column lattice

```text
A ⊕ I = {x ∈ A² : x₁ ∈ I}
```

(`TauCeti.GL2K0.lattice`), whose quotient `A² ⧸ (A ⊕ I)` is `A ⧸ I`. Over a local ring, every
submodule `L ⊆ A²` with `A² ⧸ L ≅ A ⧸ I` is a translate `γ (A ⊕ I)` with `γ ∈ GL₂(A)`: the
quotient map `A² → A ⧸ I` is given by a unimodular row of `(A ⧸ I)²`, which is the bottom row of
some `γ⁻¹` by `TauCeti.exists_bottomRowMod_eq`. So `γ ↦ γ (A ⊕ I)` identifies the left cosets
`GL₂(A) ⧸ K₀(I)` with these submodules. For a discrete valuation ring with residue field of size
`q` and `e ≥ 1` there are `qᵉ⁻¹ (q + 1)` of them, while the additive index of `O₀(𝔭ᵉ)` is `qᵉ`.
For `e = 1` these are the `q + 1` sublattices of `A²` with quotient the residue field, which index
the neighbours of `A²` in the tree of homothety classes of lattices.

## Main definitions

* `TauCeti.M2O0 I`: the standard order `O₀(I)` of `M₂(A)`.
* `TauCeti.GL2K0.lattice I`: the column lattice `A ⊕ I` of `A²`.
* `TauCeti.GL2K0.quotientLatticeEquiv I`: the isomorphism `A² ⧸ (A ⊕ I) ≃ A ⧸ I`.
* `TauCeti.GL2K0.quotientEquivLattices I`: over a local ring, `γ K₀(I) ↦ γ (A ⊕ I)` is a
  bijection from `GL₂(A) ⧸ K₀(I)` onto the submodules `L ⊆ A²` with `A² ⧸ L ≅ A ⧸ I`.

## Main results

* `TauCeti.GL2K0.eq_units_M2O0`: `K₀(I)` is the unit group of `O₀(I)`.
* `TauCeti.M2O0.index_toAddSubgroup`: `[M₂(A) : O₀(I)] = #(A ⧸ I)` as additive groups, and
  `TauCeti.M2O0.index_toAddSubgroup_maximalIdeal_pow`: `[M₂(A) : O₀(𝔭ᵉ)] = qᵉ` over a discrete
  valuation ring.
* `TauCeti.GL2K0.stabilizer_lattice`: over every commutative ring, `K₀(I)` is the stabilizer of
  `A ⊕ I` in `GL₂(A)`.
* `TauCeti.GL2K0.mem_orbit_lattice_iff`: over a local ring, the translates of `A ⊕ I` are exactly
  the submodules `L ⊆ A²` with `A² ⧸ L ≅ A ⧸ I`.
* `TauCeti.GL2K0.natCard_lattices` and `TauCeti.GL2K0.natCard_lattices_maximalIdeal_pow`: there
  are `[GL₂(A) : K₀(I)]` such submodules, which is `qᵉ⁻¹ (q + 1)` for `I = 𝔭ᵉ` with `e ≥ 1` over a
  discrete valuation ring.

## References

* J. Voight, *Quaternion Algebras*, GTM 288, 23.4.1–23.4.3 (pp. 382–383) for the standard Eichler
  order `O₀(𝔭ᵉ)`, and Lemma 26.4.1 and 26.4.3 (pp. 438–440) for the projective line of `A ⧸ I`.
-/

public section

namespace TauCeti

open Matrix
open scoped Pointwise

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The standard order `O₀(I)` -/

/-- The **standard order of level `I`**, `O₀(I) = {(a b; c d) ∈ M₂(A) : c ∈ I}`: the matrices
whose lower-left entry lies in `I`. Its unit group is the congruence level `K₀(I)`
(`TauCeti.GL2K0.eq_units_M2O0`). -/
def M2O0 : Subalgebra A (Matrix (Fin 2) (Fin 2) A) where
  carrier := {M | M 1 0 ∈ I}
  mul_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_two] at hM hN ⊢
    exact I.add_mem (I.mul_mem_right _ hM) (I.mul_mem_left _ hN)
  add_mem' hM hN := I.add_mem hM hN
  algebraMap_mem' r := by
    simp [Matrix.algebraMap_matrix_apply]

/-- `M ∈ O₀(I)` exactly when its lower-left entry lies in `I`. -/
@[simp]
theorem mem_M2O0 {M : Matrix (Fin 2) (Fin 2) A} : M ∈ M2O0 I ↔ M 1 0 ∈ I :=
  Iff.rfl

/-- An invertible matrix lies in `K₀(I)` exactly when it lies in `O₀(I)`. -/
theorem GL2K0.mem_iff_val_mem_M2O0 {g : GL (Fin 2) A} :
    g ∈ GL2K0 I ↔ (g : Matrix (Fin 2) (Fin 2) A) ∈ M2O0 I := by
  rw [GL2K0.mem_iff, mem_M2O0]

/-- **`K₀(I)` is the unit group of the standard order `O₀(I)`**: an invertible matrix lies in
`K₀(I)` exactly when it and its inverse lie in `O₀(I)`. -/
theorem GL2K0.eq_units_M2O0 : GL2K0 I = (M2O0 I).toSubmonoid.units := by
  ext g
  simp only [Submonoid.mem_units_iff, Subsemiring.mem_toSubmonoid, Subalgebra.mem_toSubsemiring,
    ← GL2K0.mem_iff_val_mem_M2O0]
  exact ⟨fun hg ↦ ⟨hg, inv_mem hg⟩, And.left⟩

/-- **The additive index of `O₀(I)`**: `[M₂(A) : O₀(I)] = #(A ⧸ I)`, the lower-left entry modulo
`I` identifying the quotient with `A ⧸ I`. When `A ⧸ I` is infinite both sides are `0`. -/
theorem M2O0.index_toAddSubgroup :
    (M2O0 I).toSubmodule.toAddSubgroup.index = Nat.card (A ⧸ I) := by
  -- The lower-left entry modulo `I` is a surjective additive map with kernel `O₀(I)`.
  let φ : Matrix (Fin 2) (Fin 2) A →+ A ⧸ I :=
    (Ideal.Quotient.mk I).toAddMonoidHom.comp (Matrix.entryAddMonoidHom A 1 0)
  have hker : φ.ker = (M2O0 I).toSubmodule.toAddSubgroup := by
    ext M
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  have hφ : Function.Surjective φ := fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Matrix.single 1 0 a, by simp [φ]⟩
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ hφ,
    AddSubgroup.card_top]

/-- **`[M₂(A) : O₀(𝔭ᵉ)] = qᵉ`** as additive groups, for a discrete valuation ring whose residue
field has `q` elements. -/
theorem M2O0.index_toAddSubgroup_maximalIdeal_pow [IsDomain A] [IsDiscreteValuationRing A]
    (e : ℕ) :
    (M2O0 (IsLocalRing.maximalIdeal A ^ e)).toSubmodule.toAddSubgroup.index =
      Nat.card (IsLocalRing.ResidueField A) ^ e := by
  rw [M2O0.index_toAddSubgroup,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]

/-! ### The lattice `A ⊕ I` and its stabilizer -/

namespace GL2K0

/-- The **column lattice `A ⊕ I`** of `A²`: the vectors whose second coordinate lies in `I`. Its
stabilizer in `GL₂(A)` is `K₀(I)` (`TauCeti.GL2K0.stabilizer_lattice`). -/
def lattice : Submodule A (Fin 2 → A) :=
  Submodule.comap (LinearMap.proj (R := A) (φ := fun _ : Fin 2 ↦ A) 1) I

variable {I}

@[simp]
theorem mem_lattice {x : Fin 2 → A} : x ∈ lattice I ↔ x 1 ∈ I :=
  Iff.rfl

/-- `x ∈ γ (A ⊕ I)` exactly when the second coordinate of `γ⁻¹ x` lies in `I`. -/
theorem mem_smul_lattice_iff {g : GL (Fin 2) A} {x : Fin 2 → A} :
    x ∈ g • lattice I ↔ (((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) *ᵥ x) 1 ∈ I :=
  -- `g⁻¹ • x` is `g⁻¹ *ᵥ x` by `Units.smul_def` and `Matrix.smul_eq_mulVec`, both `rfl`; the
  -- action of `g` on submodules is that of the matrix `g`, unfolded by the elaborator here.
  Submodule.mem_pointwise_smul_iff_inv_smul_mem

/-- Every element of `K₀(I)` carries `A ⊕ I` into itself. -/
theorem smul_lattice_le {g : GL (Fin 2) A} (hg : g ∈ GL2K0 I) : g • lattice I ≤ lattice I := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  rw [mem_iff] at hg
  rw [mem_lattice] at hx
  rw [mem_lattice, Units.smul_def, Matrix.smul_eq_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact I.add_mem (I.mul_mem_right _ hg) (I.mul_mem_left _ hx)

variable (I)

/-- **`K₀(I)` is the stabilizer of the lattice `A ⊕ I`** in `GL₂(A)`, over every commutative
ring. -/
theorem stabilizer_lattice : MulAction.stabilizer (GL (Fin 2) A) (lattice I) = GL2K0 I := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  refine ⟨fun hg ↦ ?_, fun hg ↦ le_antisymm (smul_lattice_le hg) ?_⟩
  · -- `g • (1, 0) ∈ g • (A ⊕ I) = A ⊕ I` is the first column of `g`.
    have h : g • (Pi.single 0 1 : Fin 2 → A) ∈ g • lattice I :=
      Submodule.smul_mem_pointwise_smul _ _ _ (mem_lattice.mpr (by simp))
    rw [hg, mem_lattice, Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_single_one] at h
    simpa using h
  · calc lattice I = g • g⁻¹ • lattice I := (smul_inv_smul g _).symm
      _ ≤ g • lattice I := fun x hx ↦ by
        obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
        exact Submodule.smul_mem_pointwise_smul _ _ _ (smul_lattice_le (inv_mem hg) hy)

/-! ### The quotient `A² ⧸ (A ⊕ I)` -/

/-- The second coordinate modulo `I`, a surjective linear map `A² → A ⧸ I` with kernel `A ⊕ I`. -/
private theorem ker_mkQ_comp_proj :
    LinearMap.ker (I.mkQ ∘ₗ LinearMap.proj (R := A) (φ := fun _ : Fin 2 ↦ A) 1) = lattice I := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  -- `lattice I` is defined as this preimage of `I`.
  rfl

/-- **`A² ⧸ (A ⊕ I) ≃ A ⧸ I`**, through the second coordinate modulo `I`. -/
noncomputable def quotientLatticeEquiv : ((Fin 2 → A) ⧸ lattice I) ≃ₗ[A] A ⧸ I :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_proj I).symm).trans <|
    -- Stated as `Function.Surjective` so that `quotKerEquivOfSurjective_apply_mk` applies.
    LinearMap.quotKerEquivOfSurjective _ <| show Function.Surjective _ from fun y ↦ by
      obtain ⟨a, rfl⟩ := I.mkQ_surjective y
      exact ⟨Pi.single 1 a, by simp⟩

@[simp]
theorem quotientLatticeEquiv_mk (x : Fin 2 → A) :
    quotientLatticeEquiv I (Submodule.Quotient.mk x) = Ideal.Quotient.mk I (x 1) := by
  simp [quotientLatticeEquiv]

/-- **Every translate of `A ⊕ I` has quotient `A ⧸ I`**, over every commutative ring:
`A² ⧸ γ (A ⊕ I) ≃ A ⧸ I` through `γ⁻¹` and `TauCeti.GL2K0.quotientLatticeEquiv`. -/
theorem nonempty_quotient_smul_lattice_equiv (g : GL (Fin 2) A) :
    Nonempty (((Fin 2 → A) ⧸ g • lattice I) ≃ₗ[A] A ⧸ I) := by
  refine ⟨(Submodule.Quotient.equiv _ _ (DistribMulAction.toLinearEquiv A (Fin 2 → A) g⁻¹)
    ?_).trans (quotientLatticeEquiv I)⟩
  -- The image of `g • (A ⊕ I)` under `g⁻¹` is `A ⊕ I`.
  ext x
  rw [Submodule.mem_map_equiv, mem_smul_lattice_iff]
  simp [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_mulVec]

/-! ### The submodules with quotient `A ⧸ I` -/

variable {I} in
/-- **Every submodule `L ⊆ A²` with `A² ⧸ L ≅ A ⧸ I` is a translate `γ (A ⊕ I)`**, over a local
ring. -/
theorem exists_eq_smul_lattice [IsLocalRing A] {L : Submodule A (Fin 2 → A)}
    (e : ((Fin 2 → A) ⧸ L) ≃ₗ[A] A ⧸ I) : ∃ g : GL (Fin 2) A, L = g • lattice I := by
  -- The quotient map `f : A² → A ⧸ I` has kernel `L` and sends `x` to `∑ⱼ xⱼ vⱼ`, where `v` is its
  -- row of values on the standard basis.
  let f : (Fin 2 → A) →ₗ[A] A ⧸ I := e.toLinearMap ∘ₗ L.mkQ
  let v : Fin 2 → A ⧸ I := fun j ↦ f (Pi.single j 1)
  have hf (x : Fin 2 → A) : f x = ∑ j, Ideal.Quotient.mk I (x j) * v j := by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    congr 2
    ext k
    simp [Pi.single_apply, eq_comm]
  have hL (x : Fin 2 → A) : x ∈ L ↔ f x = 0 := by
    rw [← LinearMap.mem_ker, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  -- `f` is onto, so `v` is unimodular, and it is the bottom row of some `γ` modulo `I`.
  have hv : Module.IsUnimodular (A ⧸ I) v := by
    obtain ⟨x, hx⟩ := (e.surjective.comp L.mkQ_surjective) 1
    refine TauCeti.Module.isUnimodular_pi_iff.mpr ⟨fun j ↦ Ideal.Quotient.mk I (x j), ?_⟩
    have hx' : f x = 1 := by simpa [f] using hx
    rw [hf] at hx'
    simpa [mul_comm] using hx'
  have hstable := (hasStableRangeLE_one_of_isLocalRing A).of_surjective
    (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨γ, -, hγ⟩ := exists_bottomRowMod_eq I hstable hv
  have hγv (j : Fin 2) : v j = Ideal.Quotient.mk I ((γ : Matrix (Fin 2) (Fin 2) A) 1 j) :=
    (congrFun hγ j).symm.trans (bottomRowMod_apply I γ j)
  -- So `x ∈ L ↔ f x = 0 ↔ (γ x)₁ ∈ I ↔ x ∈ γ⁻¹ (A ⊕ I)`.
  refine ⟨γ⁻¹, SetLike.ext fun x ↦ ?_⟩
  rw [hL, hf, mem_smul_lattice_iff, inv_inv, ← Ideal.Quotient.eq_zero_iff_mem]
  simp [hγv, Matrix.mulVec, dotProduct, mul_comm]

/-- **The translates of `A ⊕ I` are the submodules with quotient `A ⧸ I`**: over a local ring, a
submodule `L ⊆ A²` lies in the `GL₂(A)`-orbit of `A ⊕ I` exactly when `A² ⧸ L ≅ A ⧸ I`. -/
theorem mem_orbit_lattice_iff [IsLocalRing A] {L : Submodule A (Fin 2 → A)} :
    L ∈ MulAction.orbit (GL (Fin 2) A) (lattice I) ↔
      Nonempty (((Fin 2 → A) ⧸ L) ≃ₗ[A] A ⧸ I) := by
  refine ⟨?_, fun ⟨e⟩ ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    exact nonempty_quotient_smul_lattice_equiv I g
  · obtain ⟨g, rfl⟩ := exists_eq_smul_lattice e
    exact ⟨g, rfl⟩

/-- **`GL₂(A) ⧸ K₀(I)` is the set of submodules of `A²` with quotient `A ⧸ I`**: over a local ring,
`γ K₀(I) ↦ γ (A ⊕ I)` is a bijection. For a discrete valuation ring and `I = 𝔭ᵉ` these are the
sublattices `L ⊆ A²` with cyclic quotient `A² ⧸ L ≅ A ⧸ 𝔭ᵉ`. -/
noncomputable def quotientEquivLattices [IsLocalRing A] :
    GL (Fin 2) A ⧸ GL2K0 I ≃
      {L : Submodule A (Fin 2 → A) // Nonempty (((Fin 2 → A) ⧸ L) ≃ₗ[A] A ⧸ I)} :=
  (Subgroup.quotientEquivOfEq (stabilizer_lattice I).symm).trans <|
    (MulAction.orbitEquivQuotientStabilizer _ (lattice I)).symm.trans <|
      Equiv.subtypeEquivRight fun _ ↦ mem_orbit_lattice_iff I

@[simp]
theorem coe_quotientEquivLattices_mk [IsLocalRing A] (g : GL (Fin 2) A) :
    (quotientEquivLattices I (QuotientGroup.mk g) : Submodule A (Fin 2 → A)) = g • lattice I := by
  simp [quotientEquivLattices, Subgroup.quotientEquivOfEq_mk]

/-- **The number of submodules of `A²` with quotient `A ⧸ I`** is the index `[GL₂(A) : K₀(I)]`,
over a local ring. -/
theorem natCard_lattices [IsLocalRing A] :
    Nat.card {L : Submodule A (Fin 2 → A) // Nonempty (((Fin 2 → A) ⧸ L) ≃ₗ[A] A ⧸ I)} =
      (GL2K0 I).index := by
  rw [Subgroup.index_eq_card, Nat.card_congr (quotientEquivLattices I)]

open _root_.IsLocalRing in
/-- **There are `qᵉ⁻¹ (q + 1)` sublattices of `A²` with quotient `A ⧸ 𝔭ᵉ`**, for a discrete
valuation ring whose residue field has `q` elements and `e ≥ 1`. For `e = 1` these are the
`q + 1` sublattices with quotient the residue field. -/
theorem natCard_lattices_maximalIdeal_pow [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (ResidueField A)] {e : ℕ} (he : e ≠ 0) :
    Nat.card {L : Submodule A (Fin 2 → A) //
        Nonempty (((Fin 2 → A) ⧸ L) ≃ₗ[A] A ⧸ maximalIdeal A ^ e)} =
      Nat.card (ResidueField A) ^ (e - 1) * (Nat.card (ResidueField A) + 1) := by
  rw [natCard_lattices, GL2K0.index_maximalIdeal_pow he]

end GL2K0

end TauCeti
