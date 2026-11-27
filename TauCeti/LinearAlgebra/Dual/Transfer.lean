/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.Exact

/-!
# Transfer of module duals along a perfect trace

Let `A` be a commutative algebra over `R` and let `t : A →ₗ[R] R` have perfect
multiplication pairing. Composing with `t` identifies the `A`-valued dual of every
`A`-module with its `R`-valued dual. No freeness of the module over `A` is needed.
For a Gorenstein order with a chosen generator of its base-ring dual, this is the
comparison between order-valued and base-ring-valued lattice duals.

The inverse sends `f` to the unique functional `g` satisfying
`t (a * g m) = f (a • m)`. This is the explicit restriction–coinduction adjunction
composed with the perfect multiplication pairing. The comparison is natural in the
module and transports extension of functionals and reflexivity.

## References

* D. Burns, R. Sakamoto and T. Sano, *On the theory of higher rank Euler, Kolyvagin
  and Stark systems, II*, §4.3, for Gorenstein orders and their lattice coefficients.
-/

public section

noncomputable section

namespace LinearMap

section Semiring

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]

/-- Transfer an algebra-valued functional to a base-ring-valued functional. -/
def dualTransfer (t : A →ₗ[R] R) : (M →ₗ[A] A) →ₗ[R] (M →ₗ[R] R) where
  toFun f := t.comp (f.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The transferred functional is composition with the trace. -/
@[simp]
theorem dualTransfer_apply (t : A →ₗ[R] R) (f : M →ₗ[A] A) (m : M) :
    t.dualTransfer f m = t (f m) := (rfl)

/-- An injective multiplication pairing makes transfer injective on module duals. -/
theorem dualTransfer_injective (t : A →ₗ[R] R)
    (ht : Function.Injective ((mul R A).compr₂ t)) :
    Function.Injective (t.dualTransfer (M := M)) := by
  intro f g h
  ext m
  apply ht
  ext a
  simpa [mul_comm] using congrArg (fun l : M →ₗ[R] R ↦ l (a • m)) h

variable (t : A →ₗ[R] R) [((mul R A).compr₂ t).IsPerfPair]

/-- Every base-ring-valued functional lifts uniquely through a perfect trace. -/
theorem dualTransfer_surjective : Function.Surjective (t.dualTransfer (M := M)) := by
  let e := ((mul R A).compr₂ t).toPerfPair
  intro f
  let g (m : M) := e.symm (f.comp (((lsmul A M).flip m).restrictScalars R))
  have hg (m : M) (a : A) : t (g m * a) = f (a • m) := by
    exact congrArg (fun l : A →ₗ[R] R ↦ l a) (e.apply_symm_apply _)
  have hinj {x y : A} (h : ∀ a, t (x * a) = t (y * a)) : x = y :=
    e.injective (LinearMap.ext h)
  refine ⟨{ toFun := g
            map_add' := fun x y ↦ hinj fun a ↦ by simp [add_mul, hg]
            map_smul' := fun a m ↦ hinj fun b ↦ ?_ }, ?_⟩
  · simp only [RingHom.id_apply, smul_eq_mul]
    calc
      t (g (a • m) * b) = f (b • (a • m)) := hg _ _
      _ = f ((b * a) • m) := by rw [mul_smul]
      _ = t (g m * (b * a)) := (hg _ _).symm
      _ = t (a * g m * b) := by ac_rfl
  · ext m
    simpa using hg m 1

/-- Composition with a perfect trace identifies the algebra-valued and base-ring-valued
module duals. In particular this applies to modules over a Gorenstein order that are
free over the base ring, without requiring freeness over the order. -/
def dualTransferEquiv : (M →ₗ[A] A) ≃ₗ[R] (M →ₗ[R] R) :=
  LinearEquiv.ofBijective t.dualTransfer
    ⟨t.dualTransfer_injective (IsPerfPair.bijective_left _).injective,
      t.dualTransfer_surjective⟩

/-- Evaluation of the dual comparison. -/
@[simp]
theorem dualTransferEquiv_apply (f : M →ₗ[A] A) (m : M) :
    t.dualTransferEquiv f m = t (f m) := (rfl)

/-- The trace identity characterizing the inverse dual comparison. -/
@[simp]
theorem dualTransferEquiv_symm_apply (f : M →ₗ[R] R) (m : M) :
    t (t.dualTransferEquiv.symm f m) = f m :=
  congrArg (fun l : M →ₗ[R] R ↦ l m) (t.dualTransferEquiv.apply_symm_apply f)

/-- Naturality of the dual comparison under algebra-linear coefficient maps. -/
theorem dualTransferEquiv_comp (f : N →ₗ[A] A) (g : M →ₗ[A] N) :
    t.dualTransferEquiv (f.comp g) =
      (t.dualTransferEquiv f).comp (g.restrictScalars R) := by
  ext m
  simp

/-- Multiplying the input of an inverse-transferred functional multiplies its value
inside the trace. This characterizes the inverse without unfolding it. -/
theorem dualTransferEquiv_symm_apply_mul (f : M →ₗ[R] R) (m : M) (a : A) :
    t (a * t.dualTransferEquiv.symm f m) = f (a • m) := by
  rw [← smul_eq_mul, ← map_smul, dualTransferEquiv_symm_apply]

include t in
/-- A functional on a submodule extends whenever the inclusion splits over the base ring.
The retraction need not be algebra-linear. This gives the surjectivity at the right end
of the dual of a short exact sequence of base-ring lattices. -/
theorem exists_comp_eq_of_retraction (i : M →ₗ[A] N) (r : N →ₗ[R] M)
    (hr : r.comp (i.restrictScalars R) = .id) (f : M →ₗ[A] A) :
    ∃ g : N →ₗ[A] A, g.comp i = f := by
  refine ⟨t.dualTransferEquiv.symm ((t.dualTransferEquiv f).comp r), ?_⟩
  apply t.dualTransferEquiv.injective
  rw [dualTransferEquiv_comp, LinearEquiv.apply_symm_apply, comp_assoc, hr, comp_id]

/-- Compare the algebra-valued bidual and base-ring-valued bidual. -/
def dualTransferBidualEquiv :
    ((M →ₗ[A] A) →ₗ[A] A) ≃ₗ[R] ((M →ₗ[R] R) →ₗ[R] R) :=
  (t.dualTransferEquiv (M := M →ₗ[A] A)).trans
    (t.dualTransferEquiv (M := M)).symm.dualMap

/-- The bidual comparison intertwines the canonical evaluation maps. -/
@[simp]
theorem dualTransferBidualEquiv_eval (m : M) :
    t.dualTransferBidualEquiv (Module.Dual.eval A M m) = Module.Dual.eval R M m := by
  ext f
  simp [dualTransferBidualEquiv]

include t in
/-- Reflexivity over the algebra and over the base ring are equivalent when the trace
multiplication pairing is perfect. In particular every finite free base-ring lattice
is reflexive over a Gorenstein order equipped with a dual generator. -/
theorem isReflexive_iff_of_isPerfPair : Module.IsReflexive A M ↔ Module.IsReflexive R M := by
  constructor
  · intro h
    refine ⟨?_⟩
    have he : ⇑(Module.Dual.eval R M) =
        t.dualTransferBidualEquiv ∘ (Module.Dual.eval A M) := by
      funext m
      exact (t.dualTransferBidualEquiv_eval m).symm
    rw [he]
    exact t.dualTransferBidualEquiv.bijective.comp h.bijective_dual_eval'
  · intro h
    refine ⟨?_⟩
    have he : ⇑(Module.Dual.eval A M) =
        t.dualTransferBidualEquiv.symm ∘ (Module.Dual.eval R M) := by
      funext m
      apply t.dualTransferBidualEquiv.injective
      simp
    rw [he]
    exact t.dualTransferBidualEquiv.symm.bijective.comp h.bijective_dual_eval'

end Semiring

section Exact

variable {R A M N P : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
  (t : A →ₗ[R] R) [((mul R A).compr₂ t).IsPerfPair]

include t in
/-- Dualizing a short exact sequence with base-ring-projective quotient is surjective
on the right. Thus order-valued duality is exact on short exact sequences of lattices
over a Gorenstein order; no module need be projective over the order. -/
theorem dualMap_surjective_of_exact_of_projective [Module.Projective R P]
    (i : M →ₗ[A] N) (p : N →ₗ[A] P) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) :
    Function.Surjective i.dualMap := by
  have hexR : Function.Exact (i.restrictScalars R) (p.restrictScalars R) := hex
  obtain ⟨e, hei, -⟩ := hexR.exists_linearEquiv_prod_of_projective hi hp
  have hr : ((fst R M P).comp e.toLinearMap).comp (i.restrictScalars R) = .id := by
    rw [hei]
    ext m
    simp
  intro f
  exact t.exists_comp_eq_of_retraction i ((fst R M P).comp e.toLinearMap) hr f

end Exact

end LinearMap
