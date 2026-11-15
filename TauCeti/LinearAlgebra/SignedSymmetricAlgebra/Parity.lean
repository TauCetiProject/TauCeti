/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
public import TauCeti.RingTheory.GradedAlgebra.Coarsen
import TauCeti.Data.ZMod.IntUnitsPower

/-!
# The parity presentation of the signed symmetric algebra

The free signed algebra can be presented using only a parity grading of its generating
module. `TauCeti.ParitySignedSym` uses the native tensor algebra and the relation with sign
`(-1 : ℤˣ) ^ (i * j)` for `i j : ZMod 2`. Its universal property requires no integer lift.

For an integer grading `G`, `TauCeti.SignedSym.parityEquiv` identifies the integer presentation
with the presentation for `G.parity`, fixing every generator. This compares the quotients,
not their raw generating relations: an element homogeneous for parity can be a sum of elements
of several integer degrees. The additional parity relations already hold in the integer
quotient by bilinearity and supercommutativity.

The construction follows J. Pardon, *Contact homology and virtual fundamental cycles*,
equation (1.1) and Definition 2.48. It does not construct the grading of the parity quotient
or its odd derivations.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

/-- Signed swaps of homogeneous generators, defined using only their parities. -/
inductive paritySignedSwapRel (G : InternalGrading R V (ZMod 2)) :
    TensorAlgebra R V → TensorAlgebra R V → Prop where
  | swap (i j : ZMod 2) (x y : V) (hx : x ∈ G.piece i) (hy : y ∈ G.piece j) :
      paritySignedSwapRel G (TensorAlgebra.ι R x * TensorAlgebra.ι R y)
        (((-1 : ℤˣ) ^ (i * j)) • (TensorAlgebra.ι R y * TensorAlgebra.ι R x))

/-- The free signed algebra on a parity-graded module, without a chosen integer grading. -/
abbrev ParitySignedSym (G : InternalGrading R V (ZMod 2)) := RingQuot (paritySignedSwapRel G)

namespace ParitySignedSym

variable (G : InternalGrading R V (ZMod 2))

/-- The quotient map from the tensor algebra to the parity presentation. -/
abbrev quotient : TensorAlgebra R V →ₐ[R] ParitySignedSym G :=
  RingQuot.mkAlgHom R (paritySignedSwapRel G)

/-- Every element of the parity presentation has a tensor representative. -/
theorem quotient_surjective : Function.Surjective (quotient G) :=
  RingQuot.mkAlgHom_surjective R (paritySignedSwapRel G)

/-- The canonical linear map of generators into the parity presentation. -/
def generator : V →ₗ[R] ParitySignedSym G :=
  (quotient G).toLinearMap.comp (TensorAlgebra.ι R)

@[simp]
theorem quotient_ι (x : V) : quotient G (TensorAlgebra.ι R x) = generator G x := (rfl)

/-- The class of a tensor word is the product of its generators in the same order. -/
theorem quotient_tprod {n : ℕ} (x : Fin n → V) :
    quotient G (TensorAlgebra.tprod R V n x) =
      (List.ofFn fun i => generator G (x i)).prod := by
  simp only [TensorAlgebra.tprod_apply, map_list_prod, List.map_ofFn,
    Function.comp_def, quotient_ι]

/-- Homogeneous generators satisfy the sign rule determined by their parities. -/
theorem generator_mul_generator {i j : ZMod 2} {x y : V}
    (hx : x ∈ G.piece i) (hy : y ∈ G.piece j) :
    generator G x * generator G y = ((-1 : ℤˣ) ^ (i * j)) •
      (generator G y * generator G x) := by
  simpa only [← quotient_ι, ← map_mul, Units.smul_def, ← map_zsmul] using
    (RingQuot.mkAlgHom_rel R (paritySignedSwapRel.swap i j x y hx hy))

/-- Induction on expressions in the generating module and the coefficient ring. -/
@[elab_as_elim]
theorem induction {P : ParitySignedSym G → Prop}
    (algebraMap : ∀ r, P (algebraMap R (ParitySignedSym G) r))
    (generator : ∀ x, P (ParitySignedSym.generator G x))
    (mul : ∀ a b, P a → P b → P (a * b))
    (add : ∀ a b, P a → P b → P (a + b)) (a : ParitySignedSym G) : P a := by
  obtain ⟨a, rfl⟩ := quotient_surjective G a
  induction a using TensorAlgebra.induction with
  | algebraMap r => simpa only [AlgHom.commutes] using algebraMap r
  | ι x => exact generator x
  | mul a b ha hb => simpa only [map_mul] using mul _ _ ha hb
  | add a b ha hb => simpa only [map_add] using add _ _ ha hb

/-- Algebra maps from the parity presentation are determined on generators. -/
@[ext 1200]
theorem hom_ext {A : Type w} [Semiring A] [Algebra R A] {f g : ParitySignedSym G →ₐ[R] A}
    (h : ∀ x, f (generator G x) = g (generator G x)) : f = g := by
  apply RingQuot.ringQuot_ext'
  apply TensorAlgebra.hom_ext
  exact LinearMap.ext h

variable {A : Type w} [Ring A] [Algebra R A]

/-- Extend a linear map whose homogeneous images satisfy the parity sign rule. -/
def lift (f : V →ₗ[R] A)
    (hf : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x)) : ParitySignedSym G →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨TensorAlgebra.lift R f, by
    intro a b h
    cases h with
    | swap i j x y hx hy => simpa [Units.smul_def] using hf i j x y hx hy⟩

@[simp]
theorem lift_quotient (f : V →ₗ[R] A) (hf) (x : TensorAlgebra R V) :
    lift G f hf (quotient G x) = TensorAlgebra.lift R f x :=
  RingQuot.liftAlgHom_mkAlgHom_apply R _ _ x

@[simp]
theorem lift_generator (f : V →ₗ[R] A) (hf) (x : V) :
    lift G f hf (generator G x) = f x := by
  rw [← quotient_ι, lift_quotient, TensorAlgebra.lift_ι_apply]

/-- The extension to the parity presentation is unique. -/
theorem lift_unique (f : V →ₗ[R] A) (hf) (g : ParitySignedSym G →ₐ[R] A)
    (hg : ∀ x, g (generator G x) = f x) : g = lift G f hf := by
  apply hom_ext
  simpa only [lift_generator] using hg

/-- The universal property of the parity presentation. -/
def liftEquiv :
    {f : V →ₗ[R] A // ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x)} ≃
      (ParitySignedSym G →ₐ[R] A) where
  toFun f := lift G f.1 f.2
  invFun g := ⟨g.toLinearMap.comp (generator G), by
    intro i j x y hx hy
    simpa [Units.smul_def] using congrArg g (generator_mul_generator G hx hy)⟩
  left_inv f := Subtype.ext (LinearMap.ext fun x => lift_generator G f.1 f.2 x)
  right_inv g := by ext x; simp

@[simp]
theorem liftEquiv_apply (f) : liftEquiv G (A := A) f = lift G f.1 f.2 := (rfl)

@[simp]
theorem liftEquiv_symm_apply_val (g : ParitySignedSym G →ₐ[R] A) :
    ((liftEquiv G).symm g).val = g.toLinearMap.comp (generator G) := (rfl)

end ParitySignedSym

namespace SignedSym

variable (G : InternalGrading R V ℤ)

/-- Integer-graded generators also satisfy the relations for parity-homogeneous inputs,
which need not be homogeneous for the integer grading. -/
theorem generator_mul_generator_of_mem_parity {i j : ZMod 2} {x y : V}
    (hx : x ∈ G.parity.piece i) (hy : y ∈ G.parity.piece j) :
    generator G x * generator G y = ((-1 : ℤˣ) ^ (i * j)) •
      (generator G y * generator G x) := by
  rw [InternalGrading.parity_piece] at hx hy
  have hgen := (isHomogeneous_signedSymGenerator G).coarsenGrading
    (Int.castAddHom (ZMod 2))
  exact mul_eq_uzpow_smul_mul_of_mem_parityGrading (𝒜 := signedSymPiece G)
    (fun ha hb => by simpa [Units.smul_def] using mul_eq_negOnePow_smul_mul G ha hb)
    (by simpa only [map_zero, add_zero] using hgen.map_mem hx)
    (by simpa only [map_zero, add_zero] using hgen.map_mem hy)

private noncomputable def toParity : SignedSym G →ₐ[R] ParitySignedSym G.parity :=
  lift G (ParitySignedSym.generator G.parity) (by
    intro p q x y hx hy
    have h := ParitySignedSym.generator_mul_generator G.parity
      (by simpa only [InternalGrading.parity_piece] using mem_parityGrading_of_mem hx)
      (by simpa only [InternalGrading.parity_piece] using mem_parityGrading_of_mem hy)
    simpa only [← Int.cast_mul, uzpow_intCast_eq_negOnePow, Units.smul_def] using h)

private noncomputable def fromParity : ParitySignedSym G.parity →ₐ[R] SignedSym G :=
  ParitySignedSym.lift G.parity (generator G) (fun _ _ _ _ hx hy =>
    generator_mul_generator_of_mem_parity G hx hy)

/-- Reducing the input grading modulo two does not change the signed algebra. This equivalence
fixes the generating module and requires neither a basis nor invertibility of two. -/
noncomputable def parityEquiv : SignedSym G ≃ₐ[R] ParitySignedSym G.parity :=
  AlgEquiv.ofAlgHom (toParity G) (fromParity G)
    (by ext x; simp [toParity, fromParity])
    (by ext x; simp [toParity, fromParity])

@[simp]
theorem parityEquiv_generator (x : V) :
    parityEquiv G (generator G x) = ParitySignedSym.generator G.parity x :=
  lift_generator G _ _ x

@[simp]
theorem parityEquiv_symm_generator (x : V) :
    (parityEquiv G).symm (ParitySignedSym.generator G.parity x) = generator G x :=
  ParitySignedSym.lift_generator G.parity _ _ x

/-- The comparison commutes with the quotient maps, not only with individual generators. -/
@[simp]
theorem parityEquiv_quotient (x : TensorAlgebra R V) :
    parityEquiv G (quotient G x) = ParitySignedSym.quotient G.parity x := by
  have h : (parityEquiv G).toAlgHom.comp (quotient G) =
      ParitySignedSym.quotient G.parity := by
    apply TensorAlgebra.hom_ext
    ext x
    simp
  exact AlgHom.congr_fun h x

/-- The inverse comparison also commutes with the tensor-algebra quotient maps. -/
@[simp]
theorem parityEquiv_symm_quotient (x : TensorAlgebra R V) :
    (parityEquiv G).symm (ParitySignedSym.quotient G.parity x) = quotient G x :=
  (parityEquiv G).symm_apply_eq.2 (parityEquiv_quotient G x).symm

end SignedSym

end TauCeti
