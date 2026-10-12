/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete

/-!
# Pullback of locally constant coinduced functions

A commuting square of subgroup inclusions, together with a compatible additive coefficient
map, pulls back locally constant coinduced functions by `a ↦ (h ↦ f (a (φ h)))`.
This includes coefficient maps and restriction from an ambient group to an intermediate
subgroup. Evaluation at `1` commutes with this pullback, which gives the naturality and
restriction squares for Shapiro's lemma.

The right-translation actions and evaluation convention are those of
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, second edition, (1.6.4)
(and the footnote on p. 61, where their `Ind` denotes coinduction).
-/

public section

namespace TauCeti.DiscreteCoind

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  {U : Subgroup G} {V : Subgroup H}
  {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction U A] [DistribMulAction V B]
  (φ : H →ₜ* G) (ψ : V →ₜ* U) (hcomm : ∀ v : V, φ v = (ψ v : G))
  (f : A →+ B) (hf : ∀ (v : V) (a : A), f (ψ v • a) = v • f a)

/-- Pull back coinduced functions along a commuting square of subgroup inclusions and a
compatible coefficient map. Coefficient maps need no continuity hypothesis: the functions
are locally constant. -/
def pullback : DiscreteCoind G U A →+ DiscreteCoind H V B where
  toFun a := mk H V B (fun h => f (a (φ h)))
    (((isLocallyConstant a).comp_continuous φ.continuous).comp f)
    (fun v h => by rw [map_mul, hcomm, apply_mul, hf])
  map_zero' := ext fun h => by simp
  map_add' a b := ext fun h => by simp

/-- Pullback is precomposition on the group variable and postcomposition on coefficients. -/
@[simp]
theorem pullback_apply (a : DiscreteCoind G U A) (h : H) :
    pullback φ ψ hcomm f hf a h = f (a (φ h)) := (rfl)

/-- Evaluation at `1` commutes with pullback. -/
@[simp]
theorem eval_comp_pullback :
    (eval H V B).comp (pullback φ ψ hcomm f hf) = f.comp (eval G U A) := by
  ext a
  simp [eval_apply]

/-- Pullback intertwines the right-translation actions along the ambient homomorphism. -/
theorem pullback_smul [ContinuousMul G] [ContinuousMul H]
    (h : H) (a : DiscreteCoind G U A) :
    pullback φ ψ hcomm f hf (φ h • a) = h • pullback φ ψ hcomm f hf a := by
  ext x
  simp [coe_smul]

/-- The identity square induces the identity on coinduced functions. -/
@[simp]
theorem pullback_id :
    pullback (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id U) (fun _ => rfl)
      (AddMonoidHom.id A) (fun _ _ => rfl) = AddMonoidHom.id (DiscreteCoind G U A) := by
  ext a g
  exact pullback_apply _ _ _ _ _ a g

/-- For the identity subgroup square, pullback is the existing pointwise coinduction of
an equivariant linear coefficient map. -/
theorem pullback_id_eq_map {R : Type*} [Semiring R] [Module R A] [Module R B]
    [DistribMulAction U B] [SMulCommClass U R A] [SMulCommClass U R B]
    (q : A →ₗ[R] B) (hq : ∀ (u : U) (a : A), q (u • a) = u • q a) :
    pullback (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id U) (fun _ => rfl)
      q.toAddMonoidHom hq = (map (G := G) q hq).toAddMonoidHom := by
  ext a g
  exact (pullback_apply _ _ _ _ _ a g).trans (map_apply q hq a g).symm

/-- Pullback respects composition of subgroup squares and coefficient maps. -/
theorem pullback_comp {K : Type*} [Group K] [TopologicalSpace K] {W : Subgroup K}
    {C : Type*} [AddCommGroup C] [DistribMulAction W C]
    (φ' : K →ₜ* H) (ψ' : W →ₜ* V) (hcomm' : ∀ w : W, φ' w = (ψ' w : H))
    (f' : B →+ C) (hf' : ∀ (w : W) (b : B), f' (ψ' w • b) = w • f' b) :
    (pullback φ' ψ' hcomm' f' hf').comp (pullback φ ψ hcomm f hf) =
      pullback (φ.comp φ') (ψ.comp ψ')
        (fun w => by simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, hcomm', hcomm])
        (f'.comp f) (fun w a => by simp only [AddMonoidHom.comp_apply,
          ContinuousMonoidHom.coe_comp, Function.comp_apply, hf, hf']) := by
  ext a k
  simp

end TauCeti.DiscreteCoind
