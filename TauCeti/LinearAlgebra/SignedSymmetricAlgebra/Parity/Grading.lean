/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Basic

/-!
# The parity input-degree grading of `ParitySignedSym`

The images of the `ZMod 2` input-degree pieces of the tensor algebra form an internal parity
grading `TauCeti.paritySignedSymPiece G` of `TauCeti.ParitySignedSym G`, without choosing an
integer lift of the generator parities. Its parity-`i` piece is spanned by words of homogeneous
generators whose parities add up to `i`, multiplication adds parities, and a parity-preserving
linear map whose homogeneous images satisfy the parity sign rule lifts uniquely to a graded
algebra map.

When `G` is an internal `ℤ`-grading, reducing degrees modulo two coarsens `TauCeti.signedSymPiece G`
to `TauCeti.parityGrading (TauCeti.signedSymPiece G)`, and `TauCeti.SignedSym.parityEquiv G`
identifies this coarsened grading with `TauCeti.paritySignedSymPiece G.parity` as graded algebras.

## Main definitions

* `TauCeti.paritySignedSymPiece`: the parity-`i` piece of `TauCeti.ParitySignedSym G`.
* `TauCeti.ParitySignedSym.gradedLift` and `TauCeti.ParitySignedSym.gradedMap`: the graded
  universal property and graded functoriality.
* `TauCeti.SignedSym.toParityGraded` and `TauCeti.SignedSym.fromParityGraded`: the mutually
  inverse graded algebra maps underlying `TauCeti.SignedSym.parityEquiv`.

## Main results

* `TauCeti.isInternal_paritySignedSymPiece` and `GradedAlgebra (paritySignedSymPiece G)`.
* `TauCeti.ParitySignedSym.homogeneous_induction`: induction on homogeneous elements of fixed
  parity.
* `TauCeti.SignedSym.map_parityGrading_signedSymPiece` and
  `TauCeti.SignedSym.parityEquiv_mem_paritySignedSymPiece_iff`: `parityEquiv` identifies the
  parity coarsening of the integer grading with the native parity grading.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

namespace ParitySignedSym

variable (G : InternalGrading R V (ZMod 2))

/-- The parity swap relation ideal is homogeneous for the `ZMod 2` input-degree grading of the
tensor algebra. -/
theorem isHomogeneous_ker_quotient :
    (RingHom.ker (quotient G)).IsHomogeneous (tensorAlgebraPiece G) := by
  apply RingQuot.isHomogeneous_ker_mkAlgHom
  intro a b hab
  cases hab with
  | swap i j x y hx hy =>
    refine ⟨i + j, Submodule.sub_mem _
      (SetLike.mul_mem_graded (ι_mem_tensorAlgebraPiece G hx)
        (ι_mem_tensorAlgebraPiece G hy)) ?_⟩
    rw [Units.smul_def]
    exact zsmul_mem (by
      simpa only [add_comm] using SetLike.mul_mem_graded
        (ι_mem_tensorAlgebraPiece G hy) (ι_mem_tensorAlgebraPiece G hx)) _

end ParitySignedSym

/-- The parity-`i` piece of `ParitySignedSym G`: the image of the parity-`i` piece of the tensor
algebra under the canonical quotient map. -/
def paritySignedSymPiece (G : InternalGrading R V (ZMod 2)) (i : ZMod 2) :
    Submodule R (ParitySignedSym G) :=
  (tensorAlgebraPiece G i).map (ParitySignedSym.quotient G).toLinearMap

section Grading

variable (G : InternalGrading R V (ZMod 2))

/-- The parity-`i` piece is the image under the canonical tensor-algebra quotient map. -/
theorem paritySignedSymPiece_def (i : ZMod 2) :
    paritySignedSymPiece G i =
      (tensorAlgebraPiece G i).map (ParitySignedSym.quotient G).toLinearMap :=
  (rfl)

/-- A homogeneous class in `ParitySignedSym G` has a tensor representative of the same parity. -/
theorem mem_paritySignedSymPiece_iff {i : ZMod 2} {a : ParitySignedSym G} :
    a ∈ paritySignedSymPiece G i ↔
      ∃ x ∈ tensorAlgebraPiece G i, ParitySignedSym.quotient G x = a :=
  Submodule.mem_map

/-- The quotient map from the tensor algebra preserves input parity. -/
theorem quotient_mem_paritySignedSymPiece {i : ZMod 2} {x : TensorAlgebra R V}
    (hx : x ∈ tensorAlgebraPiece G i) :
    ParitySignedSym.quotient G x ∈ paritySignedSymPiece G i :=
  (mem_paritySignedSymPiece_iff G).2 ⟨x, hx, rfl⟩

/-- A homogeneous generator retains its parity in `ParitySignedSym G`. -/
theorem generator_mem_paritySignedSymPiece {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    ParitySignedSym.generator G x ∈ paritySignedSymPiece G i := by
  simpa only [ParitySignedSym.quotient_ι] using
    quotient_mem_paritySignedSymPiece G (ι_mem_tensorAlgebraPiece G hx)

/-- Each parity piece is spanned by words in homogeneous generators whose parities sum to `i`.
The empty word is allowed, with total parity `0`. -/
theorem paritySignedSymPiece_eq_span (i : ZMod 2) :
    paritySignedSymPiece G i = Submodule.span R
      {a | ∃ (n : ℕ) (d : Fin n → ZMod 2) (x : Fin n → V),
        (∀ k, x k ∈ G.piece (d k)) ∧ ∑ k, d k = i ∧
          a = (List.ofFn fun k ↦ ParitySignedSym.generator G (x k)).prod} := by
  rw [paritySignedSymPiece_def, tensorAlgebraPiece_eq_span, Submodule.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨n, d, x, hx, hd, rfl⟩, rfl⟩
    exact ⟨n, d, x, hx, hd, ParitySignedSym.quotient_tprod G x⟩
  · rintro ⟨n, d, x, hx, hd, rfl⟩
    exact ⟨TensorAlgebra.tprod R V n x, ⟨n, d, x, hx, hd, rfl⟩,
      ParitySignedSym.quotient_tprod G x⟩

namespace ParitySignedSym

/-- Induction on homogeneous expressions in `ParitySignedSym G`, tracking total input parity.
The zero, addition, and scalar-multiplication steps take place in each fixed parity. -/
@[elab_as_elim]
theorem homogeneous_induction {P : ZMod 2 → ParitySignedSym G → Prop}
    (one : P 0 1)
    (generator : ∀ (i : ZMod 2) (x : V), x ∈ G.piece i → P i (ParitySignedSym.generator G x))
    (mul : ∀ (i j : ZMod 2) (a b : ParitySignedSym G), P i a → P j b → P (i + j) (a * b))
    (zero : ∀ i, P i 0)
    (add : ∀ (i : ZMod 2) (a b : ParitySignedSym G), P i a → P i b → P i (a + b))
    (smul : ∀ (i : ZMod 2) (r : R) (a : ParitySignedSym G), P i a → P i (r • a))
    {i : ZMod 2} {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G i) : P i a := by
  rw [paritySignedSymPiece_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, d, x, hx, rfl, rfl⟩ := ha
    induction n with
    | zero => simpa using one
    | succ n ih =>
      simpa only [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons] using
        mul (d 0) (∑ k : Fin n, d k.succ) _ _ (generator _ _ (hx 0))
          (ih (fun k ↦ d k.succ) (fun k ↦ x k.succ) fun k ↦ hx k.succ)
  | zero => exact zero i
  | add a b _ _ ha hb => exact add i a b ha hb
  | smul r a _ ha => exact smul i r a ha

end ParitySignedSym

/-- The parity input-degree pieces of `ParitySignedSym G` form an internal direct sum. -/
theorem isInternal_paritySignedSymPiece : DirectSum.IsInternal (paritySignedSymPiece G) := by
  rw [funext (paritySignedSymPiece_def G)]
  -- `convert!` identifies the additive instances from `RingQuot` and its semiring.
  convert! GradedAlgebra.isInternal_map (tensorAlgebraPiece G) (ParitySignedSym.quotient G)
    (ParitySignedSym.quotient_surjective G) (ParitySignedSym.isHomogeneous_ker_quotient G) using 1

/-- Multiplication adds input parities in `ParitySignedSym G`. -/
instance : SetLike.GradedMonoid (paritySignedSymPiece G) where
  one_mem := by
    simpa only [map_one] using quotient_mem_paritySignedSymPiece G
      (SetLike.GradedOne.one_mem (A := tensorAlgebraPiece G))
  mul_mem _ _ _ _ ha hb := by
    obtain ⟨x, hx, rfl⟩ := (mem_paritySignedSymPiece_iff G).mp ha
    obtain ⟨y, hy, rfl⟩ := (mem_paritySignedSymPiece_iff G).mp hb
    simpa only [map_mul] using quotient_mem_paritySignedSymPiece G (SetLike.mul_mem_graded hx hy)

/-- `ParitySignedSym G` is internally `ZMod 2`-graded by input parity. -/
noncomputable instance : GradedAlgebra (paritySignedSymPiece G) :=
  (isInternal_paritySignedSymPiece G).gradedAlgebra

/-- The tensor-algebra quotient map onto `ParitySignedSym G` has parity `0`. -/
theorem isHomogeneous_paritySignedSymQuotient :
    LinearMap.IsHomogeneous (ParitySignedSym.quotient G).toLinearMap
      (tensorAlgebraPiece G) (paritySignedSymPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero, AlgHom.toLinearMap_apply] using quotient_mem_paritySignedSymPiece G hx

/-- Homogeneous parity projection commutes with the tensor-algebra quotient map. -/
@[simp]
theorem decompose_paritySignedSymQuotient (x : TensorAlgebra R V) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece G) (ParitySignedSym.quotient G x) i :
      ParitySignedSym G) =
      ParitySignedSym.quotient G
        (DirectSum.decompose (tensorAlgebraPiece G) x i : TensorAlgebra R V) := by
  have h := (isHomogeneous_paritySignedSymQuotient G).map_decompose i x
  rw [add_zero] at h
  exact h.symm

/-- The generator map into `ParitySignedSym G` preserves parity. -/
theorem isHomogeneous_paritySignedSymGenerator :
    LinearMap.IsHomogeneous (ParitySignedSym.generator G) G.piece (paritySignedSymPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using generator_mem_paritySignedSymPiece G hx

/-- The parity-`i` component of a generator is the generator of its parity-`i` component. -/
@[simp]
theorem decompose_paritySignedSymGenerator (x : V) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece G) (ParitySignedSym.generator G x) i :
      ParitySignedSym G) =
      ParitySignedSym.generator G (DirectSum.decompose G.piece x i : V) := by
  have h := (isHomogeneous_paritySignedSymGenerator G).map_decompose i x
  rw [add_zero] at h
  exact h.symm

end Grading

namespace ParitySignedSym

variable (G : InternalGrading R V (ZMod 2))
variable {A : Type w} [Ring A] [Algebra R A]
variable (𝒜 : ZMod 2 → Submodule R A)

/-- The universal extension out of `ParitySignedSym G` preserves parity when its generator
assignment does. -/
theorem isHomogeneous_lift [SetLike.GradedMonoid 𝒜] (f : V →ₗ[R] A)
    (hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) :
    LinearMap.IsHomogeneous (lift G f hr).toLinearMap (paritySignedSymPiece G) 𝒜 0 := by
  refine LinearMap.isHomogeneous_def.2 fun i a ha ↦ ?_
  obtain ⟨x, hx, rfl⟩ := (mem_paritySignedSymPiece_iff G).mp ha
  simpa only [AlgHom.toLinearMap_apply, lift_quotient] using
    (isHomogeneous_tensorAlgebraLift G 𝒜 hf).map_mem hx

variable [GradedAlgebra 𝒜]

/-- The graded universal extension of a parity-preserving generator assignment satisfying the
parity sign rule. Its underlying algebra map is `ParitySignedSym.lift`. -/
noncomputable def gradedLift (f : V →ₗ[R] A)
    (hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) : paritySignedSymPiece G →ₐᵍ[R] 𝒜 where
  toAlgHom := lift G f hr
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using (isHomogeneous_lift G 𝒜 f hr hf).map_mem hx

/-- The underlying algebra map of `gradedLift` is `lift`. -/
@[simp]
theorem gradedLift_toAlgHom (f : V →ₗ[R] A) (hr hf) :
    (gradedLift G 𝒜 f hr hf).toAlgHom = lift G f hr :=
  (rfl)

/-- The graded lift extends the given assignment on every generator. -/
@[simp]
theorem gradedLift_generator (f : V →ₗ[R] A) (hr hf) (x : V) :
    gradedLift G 𝒜 f hr hf (generator G x) = f x :=
  lift_generator G f hr x

variable {G 𝒜} in
/-- Graded algebra maps out of `ParitySignedSym G` are determined by their values on generators. -/
@[ext]
theorem gradedHom_ext {φ ψ : paritySignedSymPiece G →ₐᵍ[R] 𝒜}
    (h : ∀ x, φ (generator G x) = ψ (generator G x)) : φ = ψ := by
  have hφψ : φ.toAlgHom = ψ.toAlgHom := hom_ext G h
  exact GradedAlgHom.ext fun a ↦ DFunLike.congr_fun hφψ a

/-- The parity-preserving extension is unique among graded algebra maps. -/
theorem gradedLift_unique (f : V →ₗ[R] A) (hr hf) (φ : paritySignedSymPiece G →ₐᵍ[R] 𝒜)
    (hφ : ∀ x, φ (generator G x) = f x) : φ = gradedLift G 𝒜 f hr hf := by
  apply gradedHom_ext
  simpa only [gradedLift_generator] using hφ

section GradedMap

variable {W : Type*} [AddCommGroup W] [Module R W] (H : InternalGrading R W (ZMod 2))

/-- Functorial maps induced by parity-preserving linear maps preserve the parity grading. -/
theorem isHomogeneous_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    LinearMap.IsHomogeneous (map G H f hf).toLinearMap
      (paritySignedSymPiece G) (paritySignedSymPiece H) 0 := by
  have hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      (generator H).comp f x * (generator H).comp f y =
        ((-1 : ℤˣ) ^ (i * j)) • ((generator H).comp f y * (generator H).comp f x) :=
    fun _ _ _ _ hx hy ↦ generator_mul_generator H
      (by simpa only [add_zero] using hf.map_mem hx)
      (by simpa only [add_zero] using hf.map_mem hy)
  rw [lift_unique G ((generator H).comp f) hr (map G H f hf) (map_generator G H f hf)]
  apply isHomogeneous_lift
  simpa only [add_zero] using (isHomogeneous_paritySignedSymGenerator H).comp hf

/-- A parity-preserving linear map induces a graded algebra map of `ParitySignedSym`.
Its underlying algebra map is `ParitySignedSym.map`. -/
noncomputable def gradedMap (f : V →ₗ[R] W) (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    paritySignedSymPiece G →ₐᵍ[R] paritySignedSymPiece H where
  toAlgHom := map G H f hf
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using (isHomogeneous_map G H f hf).map_mem hx

/-- The underlying algebra map of `gradedMap` is `map`. -/
@[simp]
theorem gradedMap_toAlgHom (f : V →ₗ[R] W) (hf) :
    (gradedMap G H f hf).toAlgHom = map G H f hf :=
  (rfl)

/-- `gradedMap` agrees pointwise with `map`. -/
@[simp]
theorem gradedMap_apply (f : V →ₗ[R] W) (hf) (a : ParitySignedSym G) :
    gradedMap G H f hf a = map G H f hf a :=
  (rfl)

end GradedMap

end ParitySignedSym

/-! ### Graded comparison with an integer grading -/

namespace SignedSym

variable (G : InternalGrading R V ℤ)

/-- Reducing the integer grading of `SignedSym G` modulo two gives the image of the parity-graded
tensor algebra under the quotient map. -/
theorem parityGrading_signedSymPiece (i : ZMod 2) :
    parityGrading (signedSymPiece G) i =
      (parityGrading (tensorAlgebraPiece G) i).map (quotient G).toLinearMap := by
  refine le_antisymm (parityGrading_le_iff.2 fun p hp ↦ ?_)
    (Submodule.map_le_iff_le_comap.2 (parityGrading_le_iff.2 fun p hp x hx ↦ ?_))
  · rw [signedSymPiece_def]
    exact Submodule.map_mono fun _ hx ↦ hp ▸ mem_parityGrading_of_mem hx
  · exact hp ▸ mem_parityGrading_of_mem (quotient_mem_signedSymPiece G hx)

/-- `SignedSym.parityEquiv` carries each parity-coarsened piece of `SignedSym G` onto the
corresponding piece of `ParitySignedSym G.parity`. -/
theorem map_parityGrading_signedSymPiece (i : ZMod 2) :
    (parityGrading (signedSymPiece G) i).map (parityEquiv G).toLinearMap =
      paritySignedSymPiece G.parity i := by
  have hcomp : (parityEquiv G).toLinearMap.comp (quotient G).toLinearMap =
      (ParitySignedSym.quotient G.parity).toLinearMap :=
    LinearMap.ext (parityEquiv_quotient G)
  rw [parityGrading_signedSymPiece G i, ← Submodule.map_comp, hcomp,
    congrFun (parityGrading_tensorAlgebraPiece G) i, paritySignedSymPiece_def]

/-- `SignedSym.parityEquiv` detects membership in the parity pieces. -/
@[simp]
theorem parityEquiv_mem_paritySignedSymPiece_iff {i : ZMod 2} {a : SignedSym G} :
    parityEquiv G a ∈ paritySignedSymPiece G.parity i ↔
      a ∈ parityGrading (signedSymPiece G) i := by
  rw [← map_parityGrading_signedSymPiece G i]
  exact ⟨fun ⟨b, hb, hba⟩ ↦ (parityEquiv G).injective hba ▸ hb,
    fun ha ↦ ⟨a, ha, rfl⟩⟩

/-- The inverse of `SignedSym.parityEquiv` detects membership in the parity pieces. -/
@[simp]
theorem parityEquiv_symm_mem_parityGrading_iff {i : ZMod 2} {b : ParitySignedSym G.parity} :
    (parityEquiv G).symm b ∈ parityGrading (signedSymPiece G) i ↔
      b ∈ paritySignedSymPiece G.parity i := by
  rw [← parityEquiv_mem_paritySignedSymPiece_iff G, AlgEquiv.apply_symm_apply]

/-- An element of `SignedSym G` of integer degree `p` maps under `parityEquiv` to parity `p`. -/
theorem parityEquiv_mem_of_mem_signedSymPiece {p : ℤ} {a : SignedSym G}
    (ha : a ∈ signedSymPiece G p) :
    parityEquiv G a ∈ paritySignedSymPiece G.parity p :=
  (parityEquiv_mem_paritySignedSymPiece_iff G).2 (mem_parityGrading_of_mem ha)

/-- `SignedSym.parityEquiv` has parity `0` from `parityGrading (signedSymPiece G)` to
`paritySignedSymPiece G.parity`. -/
theorem isHomogeneous_parityEquiv :
    LinearMap.IsHomogeneous (parityEquiv G).toLinearMap
      (parityGrading (signedSymPiece G)) (paritySignedSymPiece G.parity) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
    simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
      (parityEquiv_mem_paritySignedSymPiece_iff G).2 ha

/-- The inverse of `SignedSym.parityEquiv` has parity `0`. -/
theorem isHomogeneous_parityEquiv_symm :
    LinearMap.IsHomogeneous (parityEquiv G).symm.toLinearMap
      (paritySignedSymPiece G.parity) (parityGrading (signedSymPiece G)) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hb ↦ by
    simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
      (parityEquiv_symm_mem_parityGrading_iff G).2 hb

/-- Parity projection commutes with `SignedSym.parityEquiv`. -/
@[simp]
theorem decompose_parityEquiv (a : SignedSym G) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece G.parity) (parityEquiv G a) i :
      ParitySignedSym G.parity) =
      parityEquiv G (DirectSum.decompose (parityGrading (signedSymPiece G)) a i : SignedSym G) := by
  have h := (isHomogeneous_parityEquiv G).map_decompose i a
  rw [add_zero] at h
  exact h.symm

/-- Parity projection commutes with `(SignedSym.parityEquiv G).symm`. -/
@[simp]
theorem decompose_parityEquiv_symm (b : ParitySignedSym G.parity) (i : ZMod 2) :
    (DirectSum.decompose (parityGrading (signedSymPiece G)) ((parityEquiv G).symm b) i :
      SignedSym G) =
      (parityEquiv G).symm
        (DirectSum.decompose (paritySignedSymPiece G.parity) b i : ParitySignedSym G.parity) := by
  have h := (isHomogeneous_parityEquiv_symm G).map_decompose i b
  rw [add_zero] at h
  exact h.symm

/-- `SignedSym.parityEquiv` packaged as a graded algebra map from the parity-coarsened integer
grading to the native parity grading. -/
noncomputable def toParityGraded :
    parityGrading (signedSymPiece G) →ₐᵍ[R] paritySignedSymPiece G.parity where
  toAlgHom := (parityEquiv G).toAlgHom
  map_mem ha := (parityEquiv_mem_paritySignedSymPiece_iff G).2 ha

/-- `(SignedSym.parityEquiv G).symm` packaged as a graded algebra map from the native parity
grading to the parity-coarsened integer grading. -/
noncomputable def fromParityGraded :
    paritySignedSymPiece G.parity →ₐᵍ[R] parityGrading (signedSymPiece G) where
  toAlgHom := (parityEquiv G).symm.toAlgHom
  map_mem hb := (parityEquiv_symm_mem_parityGrading_iff G).2 hb

/-- `toParityGraded` has `parityEquiv` as its underlying function. -/
@[simp]
theorem coe_toParityGraded : ⇑(toParityGraded G) = parityEquiv G :=
  (rfl)

/-- `fromParityGraded` has `(parityEquiv G).symm` as its underlying function. -/
@[simp]
theorem coe_fromParityGraded : ⇑(fromParityGraded G) = (parityEquiv G).symm :=
  (rfl)

/-- `fromParityGraded` is a left inverse to `toParityGraded` as graded algebra maps. -/
@[simp]
theorem fromParityGraded_comp_toParityGraded :
    (fromParityGraded G).comp (toParityGraded G) =
      GradedAlgHom.id R (parityGrading (signedSymPiece G)) := by
  ext a
  simp

/-- `fromParityGraded` is a right inverse to `toParityGraded` as graded algebra maps. -/
@[simp]
theorem toParityGraded_comp_fromParityGraded :
    (toParityGraded G).comp (fromParityGraded G) =
      GradedAlgHom.id R (paritySignedSymPiece G.parity) := by
  ext b
  simp

end SignedSym

end TauCeti
