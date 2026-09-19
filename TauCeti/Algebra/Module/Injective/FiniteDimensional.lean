/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Module.Injective.SelfInjective
public import TauCeti.LinearAlgebra.Dual.Cogenerator

/-!
# Finite-dimensional injective modules over a self-injective algebra

Let `A` be a finite-dimensional algebra over a field `k`, and write `D = Hom_k(-, k)`. The dual
`D(A_A)` of the right regular module is a left `A`-module, by `(a · φ) x = φ (x * a)`. This file
proves that when `A` is **right self-injective** (its regular right module is injective), every
finite-dimensional injective left `A`-module is projective. Together with
`Module.Injective.of_finite_projective`, which gives the converse from left self-injectivity, it
identifies the projective and the injective finite-dimensional modules over an algebra which is
self-injective on both sides: the projective-injective objects of the Frobenius exact category of
finite-dimensional modules.

The argument is duality, in two steps.

* `D(A_A)` is projective. Dualizing a free presentation `Aⁿ → D(A_A)` gives an embedding of `A_A`
  into the right module `D(Aⁿ)`; right self-injectivity splits it, and dualizing the splitting
  back produces a section of the presentation.
* Every finite-dimensional left module embeds into a finite power of `D(A_A)`, through the maps
  `m ↦ (x ↦ χ (x • m))` for `χ` running over a basis of `D M`. An injective module is then a
  retract of a projective one.

The left module `D(A_A)` is not installed as an instance on `Module.Dual k A` (see
`TauCeti/LinearAlgebra/Dual/RightAction.lean`). The two intermediate results therefore take an
arbitrary left `A`-module `Q` together with a `k`-linear identification `e : Q ≃ₗ[k] Dual k A`
carrying the action of `a` to precomposition with right multiplication by `a`.

## Main results

* `Module.Projective.of_linearEquiv_dual`: over a finite-dimensional right self-injective algebra,
  the left module `D(A_A)` is projective.
* `LinearEquiv.exists_injective_linearMap_pi_of_dual`: `D(A_A)` is a cogenerator for
  finite-dimensional modules; each embeds into a finite power of it.
* `Module.Projective.of_finiteDimensional_injective`: over a finite-dimensional right
  self-injective algebra, every finite-dimensional injective module is projective.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Section 3 (injective modules) and Section 15
  (quasi-Frobenius rings, where injective and projective modules coincide).
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras* I, Chapter I (the standard duality `D` and projective and injective modules).
-/

public section

namespace TauCeti

universe u v w

variable {k : Type w} [Field k] {A : Type u} [Ring A] [Algebra k A]

section Dual

variable {Q : Type*} [AddCommGroup Q] [Module A Q] [Module k Q]

/-- **The dual of the right regular module is projective over a right self-injective algebra.**
Let `A` be a finite-dimensional algebra over a field `k` whose regular right module is injective.
Any left `A`-module `Q` identified with `Module.Dual k A` by a `k`-linear equivalence `e` carrying
the action of `a` to precomposition with right multiplication by `a` is projective. -/
theorem _root_.Module.Projective.of_linearEquiv_dual [FiniteDimensional k A]
    (hA : Module.Injective Aᵐᵒᵖ A) (e : Q ≃ₗ[k] Module.Dual k A)
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) : Module.Projective A Q := by
  -- The dual `D(ₐA)` of the left regular module, as a right module: `(ψ · c) x = ψ (c * x)`.
  let : Module Aᵐᵒᵖ (Module.Dual k A) := Module.compHom _
    { toFun := fun c ↦ (LinearMap.mulLeft k c.unop).dualMap
      map_one' := by ext; simp
      map_mul' := fun _ _ ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp [add_mul] : Aᵐᵒᵖ →+* Module.End k (Module.Dual k A) }
  have hsmul (c : Aᵐᵒᵖ) (ψ : Module.Dual k A) (x : A) : (c • ψ) x = ψ (c.unop * x) := by
    -- the action is `Module.compHom` of the ring homomorphism above, applied to `ψ`
    rfl
  have : FiniteDimensional k Q := LinearEquiv.finiteDimensional e.symm
  let b := Module.finBasis k Q
  let n := Module.finrank k Q
  -- The free presentation `p : Aⁿ → Q` given by a `k`-basis of `Q`.
  let p : (Fin n → A) →ₗ[A] Q := Fintype.linearCombination A b
  have hp (a : Fin n → A) : p a = ∑ i, a i • b i := Fintype.linearCombination_apply A b a
  -- Its transpose `j : A_A → D(Aⁿ)`, an injective map of right modules.
  let j : A →ₗ[Aᵐᵒᵖ] (Fin n → Module.Dual k A) :=
    { toFun := fun x i ↦ (e (b i)).comp (LinearMap.mulLeft k x)
      map_add' := fun _ _ ↦ by ext; simp [add_mul]
      map_smul' := fun _ _ ↦ by ext; simp [hsmul] }
  have hj_apply (x y : A) (i : Fin n) : j x i y = e (b i) (x * y) := rfl
  have hj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun x hx ↦ ?_
    have h (i : Fin n) : e (b i) x = 0 := by
      simpa [hj_apply] using congr($hx i 1)
    refine (Module.forall_dual_apply_eq_zero_iff k x).1 fun φ ↦ ?_
    rw [← (b.map e).sum_repr φ]
    simp [LinearMap.sum_apply, h]
  -- Right self-injectivity splits `j`.
  obtain ⟨r, hr⟩ := Module.Injective.extension_property Aᵐᵒᵖ A _ _ j hj LinearMap.id
  have hrj (x : A) : r (j x) = x := LinearMap.congr_fun hr x
  have hr_smul (c : k) (v : Fin n → Module.Dual k A) : r (c • v) = c • r v := by
    have hv : c • v = MulOpposite.op (algebraMap k A c) • v := by
      ext i x
      simp [hsmul, ← Algebra.smul_def]
    rw [hv, map_smul, op_smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def]
  let rk : (Fin n → Module.Dual k A) →ₗ[k] A :=
    { toFun := r
      map_add' := r.map_add
      map_smul' := hr_smul }
  -- The transpose of the splitting is a section `s` of `p`.
  let s₀ (q : Q) (i : Fin n) : A :=
    (Module.evalEquiv k A).symm
      ((e q).comp (rk.comp (LinearMap.single k (fun _ ↦ Module.Dual k A) i)))
  have hs₀ (q : Q) (i : Fin n) (ψ : Module.Dual k A) : ψ (s₀ q i) = e q (r (Pi.single i ψ)) :=
    Module.apply_evalEquiv_symm_apply ..
  have hs₀_eq {q : Q} {i : Fin n} {y : A}
      (h : ∀ ψ : Module.Dual k A, ψ y = e q (r (Pi.single i ψ))) : s₀ q i = y :=
    Module.eval_apply_injective k (LinearMap.ext fun ψ ↦ by simp [hs₀, h])
  let s : Q →ₗ[A] (Fin n → A) :=
    { toFun := s₀
      map_add' := fun q q' ↦ by
        ext i
        exact hs₀_eq fun ψ ↦ by simp [hs₀]
      map_smul' := fun a q ↦ by
        ext i
        refine hs₀_eq fun ψ ↦ ?_
        have hψ : ψ (a * s₀ q i) = (MulOpposite.op a • ψ) (s₀ q i) := (hsmul _ ψ _).symm
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, hψ, hs₀, he, Pi.single_smul',
          map_smul, op_smul_eq_mul] }
  refine Module.Projective.of_split s p
    (LinearMap.ext fun q ↦ e.injective (LinearMap.ext fun x ↦ ?_))
  calc e (p (s q)) x = ∑ i, j x i (s₀ q i) := by
        simp [hp, s, he, hj_apply]
    _ = e q (r (∑ i, Pi.single i (j x i))) := by simp [hs₀]
    _ = e q x := by rw [Finset.univ_sum_single, hrj]
    _ = e (LinearMap.id q) x := rfl

end Dual

/-- **Over a finite-dimensional right self-injective algebra, finite-dimensional injective modules
are projective.** Together with `Module.Injective.of_finite_projective`, this shows that over a
finite-dimensional algebra which is self-injective on both sides the finite-dimensional projective
and injective modules coincide. -/
theorem _root_.Module.Projective.of_finiteDimensional_injective [FiniteDimensional k A]
    (hA : Module.Injective Aᵐᵒᵖ A) (M : Type v) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] [Small.{v} A] [Module.Injective A M] :
    Module.Projective A M := by
  -- The left module `D(A_A)`: `(a · φ) x = φ (x * a)`.
  let : Module A (Module.Dual k A) := Module.compHom _ (dualRightAction k A)
  have hsmul (a : A) (φ : Module.Dual k A) (x : A) : (a • φ) x = φ (x * a) :=
    (dualRightAction_apply_apply k A a φ x).trans (by rw [op_smul_eq_mul])
  have := Module.Projective.of_linearEquiv_dual hA (LinearEquiv.refl k _) hsmul
  obtain ⟨n, f, hf⟩ := (LinearEquiv.refl k _).exists_injective_linearMap_pi_of_dual hsmul M
  have : Module.Projective A (Fin n → Module.Dual k A) :=
    .of_equiv' DFinsupp.linearEquivFunOnFintype
  obtain ⟨g, hg⟩ := Module.Injective.extension_property A M _ _ f hf LinearMap.id
  exact .of_split f g hg

end TauCeti
