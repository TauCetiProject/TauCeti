/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
public import TauCeti.RepresentationTheory.BoundedContinuousFunction
public import TauCeti.RepresentationTheory.Smooth.Basic

/-!
# Bounded automorphic functions on adelic unitary groups

A bounded automorphic function is a bounded continuous complex function on the
adelic unitary group, invariant under the rational points of a framed hermitian
space, and fixed on the right by an open subgroup of the finite adelic group.
These functions form a smooth representation of the finite adelic group by right
translation. Their supremum norm is invariant under this action. Every function
has a level contained in the standard compact open subgroup.

This is the underlying space in which one imposes a convolution eigencondition
to define automorphic forms of a prescribed archimedean type.

The definition follows [ShortProof], grh-lean (https://github.com/lsernau/grh-lean),
commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
`grh/src/Lib/Adelic/AutomorphicForms/Basic.lean`
(`New.Space.IsAutomorphic`, the boundedness clause of `New.Space.IsForm`, and
`New.Space.formRep`). The construction here uses bounded continuous functions and
the subrepresentation of smooth vectors. No source code is copied.
-/

public section

noncomputable section

open BoundedContinuousFunction NumberField

namespace TauCeti.FramedHermitianSpace

variable {E ι : Type*} [Field E] [NumberField E] [IsCMField E]
  [Fintype ι] [DecidableEq ι] {s : ι → ℤˣ} (V : FramedHermitianSpace E s)

/-- The bounded automorphic functions on `V`: the left rational invariants among
the smooth vectors for finite right translation on bounded continuous functions. -/
def boundedAutomorphicFunctions :
    Subrepresentation ((rightRegular ℂ ℂ (adelicUnitaryGroup E s)).comp
      (adelicUnitaryGroup.ofFinite E s)) :=
  leftInvariantSubrepresentation ℂ ℂ V.rationalPoints (adelicUnitaryGroup.ofFinite E s) ⊓
    Representation.smoothVectors ((rightRegular ℂ ℂ (adelicUnitaryGroup E s)).comp
      (adelicUnitaryGroup.ofFinite E s))

/-- A bounded continuous function is automorphic precisely when it is invariant
under rational points and fixed by an open subgroup at the finite places. -/
@[simp]
theorem mem_boundedAutomorphicFunctions_iff (f : adelicUnitaryGroup E s →ᵇ ℂ) :
    f ∈ V.boundedAutomorphicFunctions ↔
      (∀ γ ∈ V.rationalPoints, ∀ g, f (γ * g) = f g) ∧
      ∃ K : OpenSubgroup (finiteAdelicUnitaryGroup E ι),
        ∀ k ∈ K, ∀ g, f (g * adelicUnitaryGroup.ofFinite E s k) = f g := by
  rw [boundedAutomorphicFunctions, ← SetLike.mem_coe, Subrepresentation.coe_inf,
    Set.mem_inter_iff]
  simp only [SetLike.mem_coe, mem_leftInvariantSubrepresentation_iff,
    Representation.mem_smoothVectors_iff_exists_openSubgroup]
  refine and_congr Iff.rfl ?_
  apply exists_congr
  intro K
  simp only [IsConcreteLE.le_iff, Representation.mem_stabilizer, BoundedContinuousFunction.ext_iff,
    MonoidHom.comp_apply, rightRegular_apply]
  exact ⟨fun h k hk ↦ h hk, fun h k hk ↦ h k hk⟩

/-- The space of bounded automorphic functions, carrying its inherited supremum norm. -/
abbrev BoundedAutomorphicFunction : Type _ := V.boundedAutomorphicFunctions.toSubmodule

/-- Finite right translation on bounded automorphic functions. -/
noncomputable def boundedAutomorphicRepresentation :
    Representation ℂ (finiteAdelicUnitaryGroup E ι) V.BoundedAutomorphicFunction :=
  V.boundedAutomorphicFunctions.toRepresentation

variable {V}

/-- The underlying bounded continuous function of a bounded automorphic function. -/
def BoundedAutomorphicFunction.toBoundedContinuousFunction (f : V.BoundedAutomorphicFunction) :
    adelicUnitaryGroup E s →ᵇ ℂ := f.val

instance : CoeFun V.BoundedAutomorphicFunction (fun _ ↦ adelicUnitaryGroup E s → ℂ) :=
  ⟨fun f ↦ f.toBoundedContinuousFunction⟩

/-- Bounded automorphic functions are equal when they agree at every point. -/
@[ext]
theorem BoundedAutomorphicFunction.ext {f h : V.BoundedAutomorphicFunction}
    (hfh : ∀ g, f g = h g) : f = h := by
  apply Subtype.ext
  exact BoundedContinuousFunction.ext hfh

@[simp]
theorem BoundedAutomorphicFunction.zero_apply (g : adelicUnitaryGroup E s) :
    (0 : V.BoundedAutomorphicFunction) g = 0 := (rfl)

@[simp]
theorem BoundedAutomorphicFunction.add_apply (f h : V.BoundedAutomorphicFunction)
    (g : adelicUnitaryGroup E s) : (f + h) g = f g + h g := (rfl)

@[simp]
theorem BoundedAutomorphicFunction.smul_apply (c : ℂ) (f : V.BoundedAutomorphicFunction)
    (g : adelicUnitaryGroup E s) : (c • f) g = c * f g := (rfl)

@[simp]
theorem BoundedAutomorphicFunction.neg_apply (f : V.BoundedAutomorphicFunction)
    (g : adelicUnitaryGroup E s) : (-f) g = -f g := (rfl)

@[simp]
theorem BoundedAutomorphicFunction.sub_apply (f h : V.BoundedAutomorphicFunction)
    (g : adelicUnitaryGroup E s) : (f - h) g = f g - h g := (rfl)

/-- Bounded automorphic functions are continuous. -/
@[fun_prop]
theorem BoundedAutomorphicFunction.continuous (f : V.BoundedAutomorphicFunction) :
    Continuous f := f.toBoundedContinuousFunction.continuous

/-- Bounded automorphic functions are invariant under rational points. -/
theorem BoundedAutomorphicFunction.rationalPoint_mul (f : V.BoundedAutomorphicFunction)
    {γ : adelicUnitaryGroup E s} (hγ : γ ∈ V.rationalPoints) (g : adelicUnitaryGroup E s) :
    f (γ * g) = f g :=
  ((V.mem_boundedAutomorphicFunctions_iff f.val).1 f.property).1 γ hγ g

/-- Every bounded automorphic function is fixed by an open finite subgroup. -/
theorem BoundedAutomorphicFunction.exists_openSubgroup (f : V.BoundedAutomorphicFunction) :
    ∃ K : OpenSubgroup (finiteAdelicUnitaryGroup E ι),
      ∀ k ∈ K, ∀ g, f (g * adelicUnitaryGroup.ofFinite E s k) = f g :=
  ((V.mem_boundedAutomorphicFunctions_iff f.val).1 f.property).2

/-- The finite action on functions is right translation. -/
@[simp]
theorem boundedAutomorphicRepresentation_apply (k : finiteAdelicUnitaryGroup E ι)
    (f : V.BoundedAutomorphicFunction) (g : adelicUnitaryGroup E s) :
    V.boundedAutomorphicRepresentation k f g =
      f (g * adelicUnitaryGroup.ofFinite E s k) :=
  rightRegular_apply (adelicUnitaryGroup.ofFinite E s k) f.val g

/-- Finite right translation preserves the supremum norm. -/
theorem norm_boundedAutomorphicRepresentation (k : finiteAdelicUnitaryGroup E ι)
    (f : V.BoundedAutomorphicFunction) :
    ‖V.boundedAutomorphicRepresentation k f‖ = ‖f‖ :=
  norm_rightRegular (adelicUnitaryGroup.ofFinite E s k) f.val

/-- Finite right translation is a smooth representation. -/
instance : Representation.IsSmooth V.boundedAutomorphicRepresentation := by
  unfold boundedAutomorphicRepresentation
  exact Representation.le_smoothVectors_iff.mp inf_le_right

variable (V)

/-- Constant functions are bounded automorphic functions. -/
def BoundedAutomorphicFunction.const (c : ℂ) : V.BoundedAutomorphicFunction :=
  ⟨BoundedContinuousFunction.const _ c,
    (V.mem_boundedAutomorphicFunctions_iff _).2 ⟨by simp, ⊤, by simp⟩⟩

@[simp]
theorem BoundedAutomorphicFunction.const_apply (c : ℂ) (g : adelicUnitaryGroup E s) :
    BoundedAutomorphicFunction.const V c g = c := (rfl)

/-- The norm of a constant automorphic function is the absolute value of its value. -/
theorem BoundedAutomorphicFunction.norm_const (c : ℂ) :
    ‖BoundedAutomorphicFunction.const V c‖ = ‖c‖ :=
  BoundedContinuousFunction.norm_const_eq c

/-- Construct a bounded automorphic function from a continuous, uniformly bounded
function invariant under rational points and an open finite subgroup. -/
def BoundedAutomorphicFunction.ofFunction (f : adelicUnitaryGroup E s → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C)
    (hΓ : ∀ γ ∈ V.rationalPoints, ∀ g, f (γ * g) = f g)
    (K : OpenSubgroup (finiteAdelicUnitaryGroup E ι))
    (hK : ∀ k ∈ K, ∀ g, f (g * adelicUnitaryGroup.ofFinite E s k) = f g) :
    V.BoundedAutomorphicFunction :=
  ⟨ofNormedAddCommGroup f hf C hC,
    (V.mem_boundedAutomorphicFunctions_iff _).2 ⟨hΓ, K, hK⟩⟩

@[simp]
theorem BoundedAutomorphicFunction.ofFunction_apply (f : adelicUnitaryGroup E s → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C)
    (hΓ : ∀ γ ∈ V.rationalPoints, ∀ g, f (γ * g) = f g)
    (K : OpenSubgroup (finiteAdelicUnitaryGroup E ι))
    (hK : ∀ k ∈ K, ∀ g, f (g * adelicUnitaryGroup.ofFinite E s k) = f g)
    (g : adelicUnitaryGroup E s) :
    BoundedAutomorphicFunction.ofFunction V f hf C hC hΓ K hK g = f g := (rfl)

/-- Bounded automorphic functions of level `K` are the `K`-fixed vectors. -/
def boundedAutomorphicFunctionsOfLevel (K : Subgroup (finiteAdelicUnitaryGroup E ι)) :
    Submodule ℂ V.BoundedAutomorphicFunction :=
  Representation.invariants (V.boundedAutomorphicRepresentation.comp K.subtype)

/-- The level condition is pointwise right invariance. -/
@[simp]
theorem mem_boundedAutomorphicFunctionsOfLevel_iff
    (K : Subgroup (finiteAdelicUnitaryGroup E ι)) (f : V.BoundedAutomorphicFunction) :
    f ∈ V.boundedAutomorphicFunctionsOfLevel K ↔
      ∀ k ∈ K, ∀ g, f (g * adelicUnitaryGroup.ofFinite E s k) = f g := by
  simp only [boundedAutomorphicFunctionsOfLevel, Representation.mem_invariants,
    MonoidHom.comp_apply, BoundedAutomorphicFunction.ext_iff,
    boundedAutomorphicRepresentation_apply, Subgroup.coe_subtype, Subtype.forall]

/-- Every bounded automorphic function has a compact open level inside the standard
integral subgroup. -/
theorem BoundedAutomorphicFunction.exists_isUnitaryLevel (f : V.BoundedAutomorphicFunction) :
    ∃ K : Subgroup (finiteAdelicUnitaryGroup E ι), IsUnitaryLevel K ∧
      f ∈ V.boundedAutomorphicFunctionsOfLevel K := by
  obtain ⟨U, hU⟩ := f.exists_openSubgroup
  refine ⟨(U : Subgroup _) ⊓ integralAdelicUnitaryGroup E ι,
    ⟨inf_le_right, U.isOpen.inter (isOpen_integralAdelicUnitaryGroup E ι)⟩, ?_⟩
  rw [mem_boundedAutomorphicFunctionsOfLevel_iff]
  exact fun k hk ↦ hU k hk.1

end TauCeti.FramedHermitianSpace
