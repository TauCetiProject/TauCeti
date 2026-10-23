/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Dual
import TauCeti.Algebra.Module.Injective.SelfInjective
public import TauCeti.LinearAlgebra.Dual.RightAction
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Linear duality exchanges projective and injective modules

For an algebra `A` over a field `k`, linear duality sends projective right modules to injective
left modules. Over a finite-dimensional algebra it also sends finite-dimensional injective right
modules to projective left modules. These are the projective and injective terms used when
dualizing finite module presentations.

For finite-dimensional right modules the converse also holds: the left dual is injective exactly
when the original module is projective.

The left action on a dual is specified by a linear equivalence and the identity
`e (a • q) x = e q (op a • x)`. This follows the convention of
`TauCeti.LinearAlgebra.Dual.RightAction`, avoiding a second global action on every linear dual.
The statements allow independent universes for the field, algebra, and modules.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, Sections I.3
  and I.5.

The projective-dual argument uses the existing injectivity of the dual regular module.
The injective-dual argument generalizes the transposed free-presentation proof previously in
`TauCeti.Algebra.Module.Injective.FiniteDimensional`.
-/

public section

open TauCeti

namespace LinearEquiv

universe u v w z

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {N : Type w} [AddCommGroup N] [Module Aᵐᵒᵖ N] [Module k N] [IsScalarTower k Aᵐᵒᵖ N]
  {Q : Type z} [AddCommGroup Q] [Module A Q] [Module k Q]

/-- The linear dual of a projective right module is an injective left module, with the action
given by precomposition. The algebra need not be finite-dimensional. -/
theorem moduleInjective_of_dual_projective (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x))
    [Module.Projective Aᵐᵒᵖ N] : Module.Injective A Q := by
  classical
  obtain ⟨g, hfg⟩ := Module.projective_def'.1 (inferInstance : Module.Projective Aᵐᵒᵖ N)
  let f : (N →₀ Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] N := Finsupp.linearCombination Aᵐᵒᵖ id
  -- The dual of the right regular module, with its left action.
  let : Module A (Module.Dual k A) := Module.compHom _ (dualRightAction k A)
  have hsmul (a : A) (φ : Module.Dual k A) (x : A) : (a • φ) x = φ (x * a) :=
    (dualRightAction_apply_apply k A a φ x).trans (by rw [op_smul_eq_mul])
  let : Module.Injective A (Module.Dual k A) :=
    moduleInjective_of_equiv_dual_regular k (LinearEquiv.refl k _) hsmul
  let : Module.Injective A (N → Module.Dual k A) := Module.Injective.pi A _
  -- Dualize the splitting of `N` off a free right module.
  let s : Q →ₗ[A] (N → Module.Dual k A) :=
    { toFun := fun q i ↦ (e q).comp ((f.restrictScalars k).comp
        ((Finsupp.lsingle i : Aᵐᵒᵖ →ₗ[k] N →₀ Aᵐᵒᵖ).comp
          (MulOpposite.opLinearEquiv k).toLinearMap))
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun a q ↦ by
        ext i x
        simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Finsupp.lsingle_apply,
          LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv, Function.comp_apply,
          RingHom.id_apply, Pi.smul_apply, he, hsmul]
        rw [← f.map_smul, Finsupp.smul_single, smul_eq_mul, ← MulOpposite.op_mul] }
  let r : (N → Module.Dual k A) →ₗ[A] Q :=
    { toFun := fun φ ↦ e.symm
        { toFun := fun x ↦ (g x).sum fun i c ↦ φ i c.unop
          map_add' := fun _ _ ↦ by simp [Finsupp.sum_add_index']
          map_smul' := fun _ _ ↦ by
            simp [Finsupp.sum_smul_index']
            simp only [Finsupp.sum, Finset.mul_sum] }
      map_add' := fun _ _ ↦ by apply e.injective; ext; simp [Finsupp.sum_add]
      map_smul' := fun a φ ↦ by
        apply e.injective
        ext x
        simp [he, hsmul, Finsupp.sum_smul_index'] }
  apply Module.Baer.injective
  apply (Module.Baer.of_injective
    (inferInstance : Module.Injective A (N → Module.Dual k A))).of_leftInverse s r
  intro q
  apply e.injective
  ext x
  have hx := LinearMap.congr_fun hfg x
  have hf : (g x).sum (fun i c ↦ f (Finsupp.single i c)) = x := by
    rw [← map_finsuppSum, Finsupp.sum_single]
    exact hx
  simpa [s, r, map_finsuppSum] using congr(e q $hf)

/-- Over a finite-dimensional algebra, the linear dual of a finite-dimensional injective
right module is a projective left module, with the action given by precomposition. -/
theorem moduleProjective_of_dual_injective [FiniteDimensional k A] [FiniteDimensional k N]
    [Small.{w} Aᵐᵒᵖ] [Module.Injective Aᵐᵒᵖ N] (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x)) :
    Module.Projective A Q := by
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
  -- Transpose the free presentation to an embedding of the right module `N`.
  let j : N →ₗ[Aᵐᵒᵖ] (Fin n → Module.Dual k A) :=
    { toFun := fun x i ↦ (e (b i)).comp
          (((LinearMap.toSpanSingleton Aᵐᵒᵖ N x).restrictScalars k).comp
            (MulOpposite.opLinearEquiv k).toLinearMap)
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp [hsmul, mul_smul] }
  have hj_apply (x : N) (y : A) (i : Fin n) : j x i y = e (b i) (MulOpposite.op y • x) := rfl
  have hj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun x hx ↦ ?_
    have h (i : Fin n) : e (b i) x = 0 := by
      simpa [hj_apply] using congr($hx i 1)
    refine (Module.forall_dual_apply_eq_zero_iff k x).1 fun φ ↦ ?_
    rw [← (b.map e).sum_repr φ]
    simp [LinearMap.sum_apply, h]
  -- Injectivity of the right module splits the transposed free presentation.
  obtain ⟨r, hr⟩ := Module.Injective.extension_property Aᵐᵒᵖ N _ _ j hj LinearMap.id
  have hrj (x : N) : r (j x) = x := LinearMap.congr_fun hr x
  have hr_smul (c : k) (v : Fin n → Module.Dual k A) : r (c • v) = c • r v := by
    have hv : c • v = MulOpposite.op (algebraMap k A c) • v := by
      ext i x
      simp [hsmul, ← Algebra.smul_def]
    rw [hv, r.map_smul, ← MulOpposite.algebraMap_apply, IsScalarTower.algebraMap_smul]
  let rk : (Fin n → Module.Dual k A) →ₗ[k] N :=
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
          r.map_smul] }
  refine Module.Projective.of_split s p
    (LinearMap.ext fun q ↦ e.injective (LinearMap.ext fun x ↦ ?_))
  calc e (p (s q)) x = ∑ i, j x i (s₀ q i) := by
        simp [hp, s, he, hj_apply]
    _ = e q (r (∑ i, Pi.single i (j x i))) := by simp [hs₀]
    _ = e q x := by rw [Finset.univ_sum_single, hrj]
    _ = e (LinearMap.id q) x := rfl

/-- Over a finite-dimensional algebra, a finite-dimensional right module is projective
exactly when its left scalar dual is injective. The dual action is specified by the pairing. -/
theorem moduleInjective_iff_projective_of_dual [FiniteDimensional k A]
    [FiniteDimensional k N] [Small.{z} A]
    (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x)) :
    Module.Injective A Q ↔ Module.Projective Aᵐᵒᵖ N := by
  constructor
  · intro hQ
    let : RingHomInvPair (RingEquiv.opOp A : A →+* Aᵐᵒᵖᵐᵒᵖ)
        ((RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A) :=
      RingHomInvPair.of_ringEquiv (RingEquiv.opOp A)
    let : RingHomInvPair ((RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)
        (RingEquiv.opOp A : A →+* Aᵐᵒᵖᵐᵒᵖ) :=
      RingHomInvPair.of_ringEquiv (RingEquiv.opOp A).symm
    let : Module Aᵐᵒᵖᵐᵒᵖ Q := Module.compHom Q ((RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)
    let i : Q ≃ₛₗ[(RingEquiv.opOp A : A →+* Aᵐᵒᵖᵐᵒᵖ)] Q :=
      { Equiv.refl Q with
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let := hQ
    let : Module.Injective Aᵐᵒᵖᵐᵒᵖ Q := Module.Injective.of_ringEquiv (RingEquiv.opOp A) i
    -- Record the transported action explicitly before reversing the evaluation pairing.
    have hsmul (a : Aᵐᵒᵖ) (q : Q) : MulOpposite.op a • q = a.unop • q := (rfl)
    let : Small.{z} Aᵐᵒᵖᵐᵒᵖ := small_of_injective (RingEquiv.opOp A).symm.injective
    let : IsScalarTower k Aᵐᵒᵖᵐᵒᵖ Q := IsScalarTower.of_algebraMap_smul fun c q ↦ by
      rw [MulOpposite.algebraMap_apply, hsmul, MulOpposite.algebraMap_apply,
        MulOpposite.unop_op]
      apply e.injective
      ext x
      simp [he, ← MulOpposite.algebraMap_apply]
    have : FiniteDimensional k Q := e.symm.finiteDimensional
    let d : N ≃ₗ[k] Module.Dual k Q := (Module.evalEquiv k N).trans e.dualMap
    have hd (x : N) (q : Q) : d x q = e q x := by simp [d]
    exact d.moduleProjective_of_dual_injective (A := Aᵐᵒᵖ) fun a x q ↦ by
      simpa only [hd, hsmul, MulOpposite.op_unop] using (he a.unop q x).symm
  · intro hN
    let := hN
    exact e.moduleInjective_of_dual_projective he

end LinearEquiv
