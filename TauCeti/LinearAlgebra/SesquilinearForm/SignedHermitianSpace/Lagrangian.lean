/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Hyperbolic

/-!
# Lagrangians and complete hyperbolic splittings

A Lagrangian of a signed hermitian space is a submodule equal to its orthogonal. Over a field
with nontrivial involution, a finite-dimensional Lagrangian admits a complementary Lagrangian.
More precisely, any prescribed basis of the Lagrangian extends to a complete hyperbolic frame:
the resulting isometry from a hyperbolic space sends its first coordinate vectors to that basis.
The ambient space need not be assumed finite-dimensional.

Complete splittings are expressed using the existing `SignedHermitianSpace.IsometryEquiv`
rather than a second bundle of frames. The coordinate characterization identifies a Lagrangian
with the vectors whose second hyperbolic coordinate vanishes. These coordinates are the
algebraic input for parabolic subgroups and zero terms of theta functions.

The construction extends the prescribed basis using
`SignedHermitianSpace.exists_isHyperbolicFrame`. Subtracting the component dual to the first
frame leaves a vector orthogonal to that frame, hence in the Lagrangian and in its span.
No choice of a second basis of the Lagrangian is required.
-/

public noncomputable section

open Module

namespace TauCeti.SignedHermitianSpace

section CommRing

variable {K V V' : Type*} [CommRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] {σ : K →+* K} {ε : ℤˣ}
  {H : SignedHermitianSpace K V σ ε} {H' : SignedHermitianSpace K V' σ ε}
  {U : Submodule K V}

/-- A Lagrangian is a submodule equal to its orthogonal for the signed hermitian form. -/
def IsLagrangian (H : SignedHermitianSpace K V σ ε) (U : Submodule K V) : Prop :=
  U.orthogonalBilin H.form = U

/-- The defining self-orthogonality condition for a Lagrangian. -/
theorem isLagrangian_iff : H.IsLagrangian U ↔ U.orthogonalBilin H.form = U := Iff.rfl

/-- Membership in a Lagrangian is equivalent to pairing to zero with all of it. -/
theorem IsLagrangian.mem_iff (hU : H.IsLagrangian U) {v : V} :
    v ∈ U ↔ ∀ u ∈ U, H.form u v = 0 := by
  rw [← Submodule.mem_orthogonalBilin, hU]

/-- The form vanishes on pairs of vectors of a Lagrangian. -/
theorem IsLagrangian.form_eq_zero (hU : H.IsLagrangian U) {u v : V}
    (hu : u ∈ U) (hv : v ∈ U) : H.form u v = 0 :=
  hU.mem_iff.mp hv u hu

/-- A Lagrangian contains every totally isotropic submodule containing it. -/
theorem IsLagrangian.eq_of_le (hU : H.IsLagrangian U) {W : Submodule K V}
    (hUW : U ≤ W) (hW : W ≤ W.orthogonalBilin H.form) : U = W := by
  apply le_antisymm hUW
  intro w hw
  exact hU.mem_iff.mpr fun u hu ↦ Submodule.mem_orthogonalBilin.mp (hW hw) u (hUW hu)

/-- Isometries carry Lagrangians to Lagrangians. -/
theorem IsLagrangian.map (hU : H.IsLagrangian U) (f : IsometryEquiv H H') :
    H'.IsLagrangian (U.map f.toLinearEquiv.toLinearMap) := by
  ext v
  obtain ⟨v, rfl⟩ := f.surjective v
  simp only [Submodule.mem_orthogonalBilin, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨v, hU.mem_iff.mpr ?_, rfl⟩
    intro u hu
    simpa using hv (f u) ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, huf⟩ w ⟨z, hz, rfl⟩
    have huv : u = v := f.injective huf
    subst u
    simpa using hU.form_eq_zero hz hu

/-- Isometric transport preserves and reflects the Lagrangian condition. -/
@[simp]
theorem isLagrangian_map_iff (f : IsometryEquiv H H') :
    H'.IsLagrangian (U.map f.toLinearEquiv.toLinearMap) ↔ H.IsLagrangian U := by
  constructor
  · intro hU
    have h := hU.map f.symm
    simpa only [← Submodule.map_comp, IsometryEquiv.toLinearEquiv_symm,
      LinearEquiv.symm_comp, Submodule.map_id] using h
  · exact fun hU ↦ hU.map f

variable [RingHomInvPair σ σ] {ι : Type*} [Fintype ι]

/-- The first coordinate subspace of a hyperbolic space is Lagrangian. -/
@[simp]
theorem isLagrangian_range_inl_hyperbolic :
    (hyperbolic K σ ε ι).IsLagrangian (LinearMap.range (LinearMap.inl K (ι → K) (ι → K))) := by
  classical
  ext v
  simp only [Submodule.mem_orthogonalBilin, LinearMap.mem_range]
  constructor
  · intro hv
    have hv₂ : v.2 = 0 := funext fun i ↦ by
      simpa [Pi.single_apply] using hv (Pi.single i 1, 0) ⟨Pi.single i 1, rfl⟩
    exact ⟨v.1, Prod.ext rfl hv₂.symm⟩
  · rintro ⟨a, rfl⟩ w ⟨b, rfl⟩
    simp

/-- The second coordinate subspace of a hyperbolic space is Lagrangian. -/
@[simp]
theorem isLagrangian_range_inr_hyperbolic :
    (hyperbolic K σ ε ι).IsLagrangian (LinearMap.range (LinearMap.inr K (ι → K) (ι → K))) := by
  classical
  ext v
  simp only [Submodule.mem_orthogonalBilin, LinearMap.mem_range]
  constructor
  · intro hv
    have hv₁ : v.1 = 0 := funext fun i ↦ by
      have hi := hv (0, Pi.single i 1) ⟨Pi.single i 1, rfl⟩
      simpa [Pi.single_apply, smul_smul] using congrArg (ε • ·) hi
    exact ⟨v.2, Prod.ext hv₁.symm rfl⟩
  · rintro ⟨a, rfl⟩ w ⟨b, rfl⟩
    simp

omit [RingHomInvPair σ σ] in
/-- Dual frames span the whole space if the first frame spans a Lagrangian. The second frame
need not be isotropic, and the scalars need only form a commutative ring. -/
theorem surjective_hyperbolicFrameMap_of_isLagrangian [DecidableEq ι]
    {x y : ι → V} (hxy : ∀ i j, H.form (x i) (y j) = if i = j then 1 else 0)
    (hU : H.IsLagrangian (Submodule.span K (Set.range x))) :
    Function.Surjective (hyperbolicFrameMap K x y) := by
  intro v
  let w := v - ∑ i, H.form (x i) v • y i
  have hw : w ∈ Submodule.span K (Set.range x) := by
    rw [← hU, Submodule.mem_orthogonalBilin_span]
    rintro _ ⟨j, rfl⟩
    simp [w, map_sum, hxy]
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw
  refine ⟨(a, fun i ↦ H.form (x i) v), ?_⟩
  rw [hyperbolicFrameMap_apply, ha]
  exact sub_add_cancel _ _

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {σ : K →+* K} [RingHomInvPair σ σ] {ε : ℤˣ}
  {H : SignedHermitianSpace K V σ ε} {U : Submodule K V}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Any prescribed basis of a finite-dimensional Lagrangian extends to a complete hyperbolic
splitting, with that basis as its first coordinate vectors. The involution must be nontrivial;
there is no characteristic restriction. -/
theorem IsLagrangian.exists_isometryEquiv_apply_inl_eq (hU : H.IsLagrangian U)
    (hσ : ∃ z, σ z ≠ z) (b : Basis ι K U) :
    ∃ f : IsometryEquiv (hyperbolic K σ ε ι) H,
      ∀ i, f (Pi.single i 1, 0) = (b i : V) := by
  classical
  let x : ι → V := fun i ↦ b i
  have hx : LinearIndependent K x := b.linearIndependent.map' U.subtype U.ker_subtype
  have hspan : Submodule.span K (Set.range x) = U := by
    calc
      _ = (Submodule.span K (Set.range b)).map U.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = U := by rw [b.span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨y, hxy⟩ := H.exists_isHyperbolicFrame hσ hx
    fun i j ↦ hU.form_eq_zero (b i).property (b j).property
  let f : IsometryEquiv (hyperbolic K σ ε ι) H :=
    { LinearEquiv.ofBijective (hyperbolicFrameMap K x y)
        ⟨hxy.injective_hyperbolicFrameMap,
          surjective_hyperbolicFrameMap_of_isLagrangian hxy.form_left_right (hspan ▸ hU)⟩ with
      map_app' := hxy.form_hyperbolicFrameMap }
  refine ⟨f, fun i ↦ ?_⟩
  -- The constructed equivalence has the frame map as its underlying linear map.
  change hyperbolicFrameMap K x y (Pi.single i 1, 0) = (b i : V)
  simp [hyperbolicFrameMap_apply, Pi.single_apply, x]

/-- A finite-dimensional Lagrangian is the first coordinate subspace of a complete hyperbolic
splitting. This gives the splitting without fixing a basis of the Lagrangian in advance. -/
theorem IsLagrangian.exists_isometryEquiv_map_range_inl_eq [FiniteDimensional K U]
    (hU : H.IsLagrangian U) (hσ : ∃ z, σ z ≠ z) :
    ∃ f : IsometryEquiv (hyperbolic K σ ε (Fin (finrank K U))) H,
      (LinearMap.range (LinearMap.inl K _ _)).map f.toLinearEquiv.toLinearMap = U := by
  obtain ⟨f, hf⟩ := hU.exists_isometryEquiv_apply_inl_eq hσ (Module.finBasis K U)
  refine ⟨f, ?_⟩
  rw [← LinearMap.range_comp]
  have heq : f.toLinearEquiv.toLinearMap.comp (LinearMap.inl K _ _) =
      U.subtype.comp (Module.finBasis K U).equivFun.symm.toLinearMap := by
    apply (Pi.basisFun K (Fin (finrank K U))).ext
    intro i
    simpa using hf i
  rw [heq, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

/-- Self-orthogonality characterizes the first coordinate subspaces of complete hyperbolic
splittings over a field with nontrivial involution. -/
theorem isLagrangian_iff_exists_isometryEquiv [FiniteDimensional K U]
    (hσ : ∃ z, σ z ≠ z) :
    H.IsLagrangian U ↔
      ∃ f : IsometryEquiv (hyperbolic K σ ε (Fin (finrank K U))) H,
        (LinearMap.range (LinearMap.inl K _ _)).map f.toLinearEquiv.toLinearMap = U := by
  refine ⟨fun hU ↦ hU.exists_isometryEquiv_map_range_inl_eq hσ, ?_⟩
  rintro ⟨f, hf⟩
  simpa only [hf] using isLagrangian_range_inl_hyperbolic.map f

end Field

end TauCeti.SignedHermitianSpace
