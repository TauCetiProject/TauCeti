/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.RingQuot
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Basic
public import TauCeti.LinearAlgebra.TensorAlgebra.Grading
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# The input-degree grading of the signed symmetric algebra

The images of the input-degree pieces of the tensor algebra form an internal integer grading
of `TauCeti.SignedSym G`. Equivalently, its degree-`p` piece is spanned by words of homogeneous
generators whose degrees sum to `p`. Multiplication adds degrees, and a degree-preserving
linear map satisfying the Koszul relations extends to a graded algebra map.

The construction of the free supercommutative algebra follows J. Pardon,
*Contact homology and virtual fundamental cycles*, equation (1.1). Grading descent uses
`TwoSidedIdeal.homogeneous_span` and `TauCeti.GradedAlgebra.isInternal_quotientPiece`, transported
back to the actual `RingQuot` carrier by Mathlib's first isomorphism theorem. The grading and
its universal property require no basis, flatness, or restriction on the characteristic.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

namespace SignedSym

variable (G : InternalGrading R V)

/-- The Koszul relation ideal is homogeneous for tensor input degree. -/
theorem isHomogeneous_ker_quotient :
    (RingHom.ker (quotient G)).IsHomogeneous (tensorAlgebraPiece G) := by
  rw [quotient, AlgHom.ker_coe, RingQuot.mkAlgHom_coe, RingQuot.ker_mkRingHom_eq_span]
  refine TwoSidedIdeal.homogeneous_span _ ?_
  rintro _ ⟨a, b, hab, rfl⟩
  cases hab with
  | swap p q x y hx hy =>
    refine ⟨p + q, Submodule.sub_mem _
      (SetLike.mul_mem_graded (ι_mem_tensorAlgebraPiece G hx)
        (ι_mem_tensorAlgebraPiece G hy)) ?_⟩
    exact zsmul_mem (by
      simpa only [add_comm] using SetLike.mul_mem_graded
        (ι_mem_tensorAlgebraPiece G hy) (ι_mem_tensorAlgebraPiece G hx)) _

end SignedSym

/-- The degree-`p` piece of the signed symmetric algebra: the image of the input-degree-`p`
piece of the tensor algebra. -/
noncomputable def signedSymPiece (G : InternalGrading R V) (p : ℤ) :
    Submodule R (SignedSym G) :=
  (tensorAlgebraPiece G p).map (SignedSym.quotient G).toLinearMap

variable (G : InternalGrading R V)

/-- The piece is the image under the canonical tensor-algebra quotient map. -/
theorem signedSymPiece_def (p : ℤ) :
    signedSymPiece G p = (tensorAlgebraPiece G p).map (SignedSym.quotient G).toLinearMap := (rfl)

/-- A homogeneous class has a tensor representative of the same input degree. -/
@[simp]
theorem mem_signedSymPiece_iff {p : ℤ} {a : SignedSym G} :
    a ∈ signedSymPiece G p ↔
      ∃ x ∈ tensorAlgebraPiece G p, SignedSym.quotient G x = a :=
  Submodule.mem_map

/-- The quotient map preserves input degree. -/
theorem quotient_mem_signedSymPiece {p : ℤ} {x : TensorAlgebra R V}
    (hx : x ∈ tensorAlgebraPiece G p) :
    SignedSym.quotient G x ∈ signedSymPiece G p :=
  (mem_signedSymPiece_iff G).2 ⟨x, hx, rfl⟩

/-- A homogeneous generator retains its degree in the signed symmetric algebra. -/
theorem generator_mem_signedSymPiece {p : ℤ} {x : V} (hx : x ∈ G.piece p) :
    SignedSym.generator G x ∈ signedSymPiece G p := by
  simpa only [SignedSym.quotient_ι] using
    quotient_mem_signedSymPiece G (ι_mem_tensorAlgebraPiece G hx)

/-- A homogeneous piece is spanned by words in homogeneous generators of the indicated total
degree. The empty word is allowed, with total degree zero. -/
theorem signedSymPiece_eq_span (p : ℤ) :
    signedSymPiece G p = Submodule.span R {a | ∃ (n : ℕ) (d : Fin n → ℤ) (x : Fin n → V),
      (∀ i, x i ∈ G.piece (d i)) ∧ ∑ i, d i = p ∧
        a = (List.ofFn fun i => SignedSym.generator G (x i)).prod} := by
  rw [signedSymPiece_def, tensorAlgebraPiece_eq_span, Submodule.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨n, d, x, hx, hd, rfl⟩, rfl⟩
    exact ⟨n, d, x, hx, hd, SignedSym.quotient_tprod G x⟩
  · rintro ⟨n, d, x, hx, hd, rfl⟩
    exact ⟨TensorAlgebra.tprod R V n x, ⟨n, d, x, hx, hd, rfl⟩,
      SignedSym.quotient_tprod G x⟩

/-- The input-degree pieces of the signed symmetric algebra form an internal direct sum. -/
theorem isInternal_signedSymPiece : DirectSum.IsInternal (signedSymPiece G) := by
  let I := RingHom.ker (SignedSym.quotient G)
  let e := Ideal.quotientKerAlgEquivOfSurjective (SignedSym.quotient_surjective G)
  let H : InternalGrading R (TensorAlgebra R V ⧸ I) :=
    ⟨GradedAlgebra.quotientPiece (tensorAlgebraPiece G) I,
      GradedAlgebra.isInternal_quotientPiece _ _ (SignedSym.isHomogeneous_ker_quotient G)⟩
  have hp : (H.map e.toLinearEquiv).piece = signedSymPiece G := by
    funext p
    rw [InternalGrading.map_piece]
    dsimp only [H]
    rw [GradedAlgebra.quotientPiece_def, ← Submodule.map_comp, signedSymPiece]
    apply congrArg ((tensorAlgebraPiece G p).map)
    exact LinearMap.ext fun x =>
      Ideal.quotientKerAlgEquivOfSurjective_mk (SignedSym.quotient_surjective G) x
  rw [← hp]
  exact (H.map e.toLinearEquiv).isInternal

/-- Multiplication adds input degrees in the signed symmetric algebra. -/
instance : SetLike.GradedMonoid (signedSymPiece G) where
  one_mem := by
    simpa only [map_one] using quotient_mem_signedSymPiece G
      (SetLike.GradedOne.one_mem (A := tensorAlgebraPiece G))
  mul_mem i j a b ha hb := by
    obtain ⟨x, hx, rfl⟩ := (mem_signedSymPiece_iff G).mp ha
    obtain ⟨y, hy, rfl⟩ := (mem_signedSymPiece_iff G).mp hb
    simpa only [map_mul] using quotient_mem_signedSymPiece G (SetLike.mul_mem_graded hx hy)

/-- The signed symmetric algebra is internally graded by input degree. -/
noncomputable instance : GradedAlgebra (signedSymPiece G) :=
  (isInternal_signedSymPiece G).gradedAlgebra

/-- The tensor-algebra quotient map has degree zero. -/
theorem isHomogeneous_signedSymQuotient :
    LinearMap.IsHomogeneous (SignedSym.quotient G).toLinearMap
      (tensorAlgebraPiece G) (signedSymPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx => by
    simpa only [add_zero, AlgHom.toLinearMap_apply] using quotient_mem_signedSymPiece G hx

/-- Homogeneous projection commutes with the tensor-algebra quotient map. -/
@[simp]
theorem decompose_signedSymQuotient (x : TensorAlgebra R V) (p : ℤ) :
    (DirectSum.decompose (signedSymPiece G) (SignedSym.quotient G x) p : SignedSym G) =
      SignedSym.quotient G
        (DirectSum.decompose (tensorAlgebraPiece G) x p : TensorAlgebra R V) := by
  have h := (isHomogeneous_signedSymQuotient G).map_decompose p x
  rw [add_zero] at h
  exact h.symm

/-- The generator map has degree zero for the input-degree grading. -/
theorem isHomogeneous_signedSymGenerator :
    LinearMap.IsHomogeneous (SignedSym.generator G) G.piece (signedSymPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx => by
    simpa only [add_zero] using generator_mem_signedSymPiece G hx

/-- The degree-`p` component of a generator is the generator of its degree-`p` component. -/
@[simp]
theorem decompose_signedSymGenerator (x : V) (p : ℤ) :
    (DirectSum.decompose (signedSymPiece G) (SignedSym.generator G x) p : SignedSym G) =
      SignedSym.generator G (DirectSum.decompose G.piece x p : V) := by
  have h := (isHomogeneous_signedSymGenerator G).map_decompose p x
  rw [add_zero] at h
  exact h.symm

namespace SignedSym

variable {A : Type w} [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A)

/-- The universal extension preserves input degree when its generator assignment does. -/
theorem isHomogeneous_lift [SetLike.GradedMonoid 𝒜] (f : V →ₗ[R] A)
    (hr : ∀ (p q : ℤ) (x y : V), x ∈ G.piece p → y ∈ G.piece q →
      f x * f y = ((p * q).negOnePow : ℤ) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) :
    LinearMap.IsHomogeneous (lift G f hr).toLinearMap (signedSymPiece G) 𝒜 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p a ha => ?_
  obtain ⟨x, hx, rfl⟩ := (mem_signedSymPiece_iff G).mp ha
  simpa only [AlgHom.toLinearMap_apply, lift_quotient] using
    (isHomogeneous_tensorAlgebraLift G 𝒜 hf).map_mem hx

variable [GradedAlgebra 𝒜]

/-- The graded universal extension of a degree-preserving generator assignment satisfying
the Koszul relations. Its underlying algebra map is `SignedSym.lift`. -/
noncomputable def gradedLift (f : V →ₗ[R] A)
    (hr : ∀ (p q : ℤ) (x y : V), x ∈ G.piece p → y ∈ G.piece q →
      f x * f y = ((p * q).negOnePow : ℤ) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) : signedSymPiece G →ₐᵍ[R] 𝒜 where
  toAlgHom := lift G f hr
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using (isHomogeneous_lift G 𝒜 f hr hf).map_mem hx

@[simp]
theorem gradedLift_toAlgHom (f : V →ₗ[R] A) (hr hf) :
    (gradedLift G 𝒜 f hr hf).toAlgHom = lift G f hr := (rfl)

/-- The graded lift extends the given assignment on every generator. -/
@[simp]
theorem gradedLift_generator (f : V →ₗ[R] A) (hr hf) (x : V) :
    gradedLift G 𝒜 f hr hf (generator G x) = f x :=
  lift_generator G f hr x

variable {G 𝒜} in
/-- Graded algebra maps out of the signed symmetric algebra are determined by generators. -/
@[ext]
theorem gradedHom_ext {φ ψ : signedSymPiece G →ₐᵍ[R] 𝒜}
    (h : ∀ x, φ (generator G x) = ψ (generator G x)) : φ = ψ := by
  have hφψ : φ.toAlgHom = ψ.toAlgHom := hom_ext G h
  exact GradedAlgHom.ext fun a => DFunLike.congr_fun hφψ a

/-- The degree-preserving extension is unique among graded algebra maps. -/
theorem gradedLift_unique (f : V →ₗ[R] A) (hr hf) (φ : signedSymPiece G →ₐᵍ[R] 𝒜)
    (hφ : ∀ x, φ (generator G x) = f x) : φ = gradedLift G 𝒜 f hr hf := by
  apply gradedHom_ext
  simpa only [gradedLift_generator] using hφ

section Map

variable {W : Type*} [AddCommGroup W] [Module R W] (H : InternalGrading R W)

/-- Functorial maps induced by degree-preserving linear maps preserve the quotient grading. -/
theorem isHomogeneous_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    LinearMap.IsHomogeneous (map G H f hf).toLinearMap
      (signedSymPiece G) (signedSymPiece H) 0 := by
  have hr : ∀ (p q : ℤ) (x y : V), x ∈ G.piece p → y ∈ G.piece q →
      (generator H).comp f x * (generator H).comp f y =
        ((p * q).negOnePow : ℤ) • ((generator H).comp f y * (generator H).comp f x) := by
    intro p q x y hx hy
    exact generator_mul_generator H
      (by simpa only [add_zero] using hf.map_mem hx)
      (by simpa only [add_zero] using hf.map_mem hy)
  rw [lift_unique G ((generator H).comp f) hr (map G H f hf) (map_generator G H f hf)]
  apply isHomogeneous_lift
  simpa only [add_zero] using (isHomogeneous_signedSymGenerator H).comp hf

end Map

end SignedSym

end TauCeti
