/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.Dual.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Retract
import Mathlib.LinearAlgebra.Projection

/-!
# Projective summands of the Auslander–Reiten transpose

The transpose of a finite minimal projective presentation has no nonzero projective
retract. This removes the projective ambiguity in the stable transpose construction:
when passing back to actual modules, a minimal transpose contributes no projective summands.
In particular, such a transpose is projective exactly when it is zero.

The results hold over an arbitrary ring. Only the two presenting projectives need be
finitely generated; no finiteness is required of the projective retract. More generally,
the statements apply to any map between finite projectives whose kernel is superfluous,
without specifying an augmentation to a presented module.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.IsSuperfluous

open CategoryTheory CategoryTheory.Limits

variable {A P₀ P₁ : Type*} [Ring A]
  [AddCommMonoid P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]
  {p₁ : P₁ →ₗ[A] P₀}

/-- The transpose of a map between finite projectives with superfluous kernel has no
nonzero projective retract. In particular, this applies to finite minimal presentations. -/
theorem subsingleton_of_retract_auslanderReitenTranspose
    (h : IsSuperfluous (LinearMap.ker p₁))
    {Q : Type*} [AddCommMonoid Q] [Module Aᵐᵒᵖ Q] [Module.Projective Aᵐᵒᵖ Q]
    (r : AuslanderReitenTranspose p₁ →ₗ[Aᵐᵒᵖ] Q)
    (s : Q →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁)
    (hrs : r ∘ₗ s = LinearMap.id) : Subsingleton Q := by
  let q := AuslanderReitenTranspose.mk p₁
  obtain ⟨l, hl⟩ := Module.projective_lifting_property q s
    (AuslanderReitenTranspose.mk_surjective p₁)
  -- Lift the projection onto the retract to the dual of P₁, then use finite-projective
  -- reflexivity to regard it as the dual of an endomorphism of P₁.
  obtain ⟨u, hu⟩ := (opDual_lcomp_bijective A P₁).surjective (l ∘ₗ r ∘ₗ q)
  have hu_apply (φ : Module.Dual A P₁) : u.lcomp Aᵐᵒᵖ A φ = l (r (q φ)) :=
    LinearMap.congr_fun hu φ
  have hl_apply (x : Q) : q (l x) = s x := LinearMap.congr_fun hl x
  have hrs_apply (x : Q) : r (s x) = x := LinearMap.congr_fun hrs x
  have hidem : IsIdempotentElem u := by
    apply (opDual_lcomp_bijective A P₁).injective
    ext φ x
    have heq : u.lcomp Aᵐᵒᵖ A (u.lcomp Aᵐᵒᵖ A φ) = u.lcomp Aᵐᵒᵖ A φ := by
      simp only [hu_apply, hl_apply, hrs_apply]
    exact LinearMap.congr_fun heq x
  -- The lifted idempotent kills the dual presenting map, so its original image lies
  -- in the superfluous kernel of p₁. An idempotent's image is also a direct summand.
  have hp : p₁ ∘ₗ u = 0 := by
    apply (opDual_lcomp_bijective A P₀).injective
    ext φ x
    have heq : u.lcomp Aᵐᵒᵖ A (p₁.lcomp Aᵐᵒᵖ A φ) = 0 := by
      simp [hu_apply, q]
    simpa only [LinearMap.lcomp_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
      LinearMap.congr_fun heq x
  have hrange : LinearMap.range u ≤ LinearMap.ker p₁ :=
    LinearMap.range_le_ker_iff.mpr hp
  have hu_zero : u = 0 := LinearMap.range_eq_bot.mp
    ((h.mono hrange).eq_bot_of_isCompl (LinearMap.IsIdempotentElem.isCompl hidem))
  have hl_zero (x : Q) : l x = 0 := by
    obtain ⟨φ, hφ⟩ := AuslanderReitenTranspose.mk_surjective p₁ (s x)
    have heq := hu_apply φ
    simpa [hu_zero, q, hφ, hrs_apply, LinearMap.lcomp_apply'] using heq.symm
  have hs_zero (x : Q) : s x = 0 := by
    rw [← hl_apply, hl_zero, map_zero]
  exact ⟨fun x y ↦ by
    have hx : x = 0 := by rw [← hrs_apply x, hs_zero, map_zero]
    have hy : y = 0 := by rw [← hrs_apply y, hs_zero, map_zero]
    exact hx.trans hy.symm⟩

/-- A projective module retract of a transpose with superfluous presenting kernel is zero. -/
theorem isZero_of_retract_auslanderReitenTranspose
    (h : IsSuperfluous (LinearMap.ker p₁)) {Q : ModuleCat Aᵐᵒᵖ}
    (r : Retract Q (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p₁)))
    [Projective Q] : IsZero Q := by
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (h.subsingleton_of_retract_auslanderReitenTranspose r.r.hom r.i.hom (by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using
        congrArg ModuleCat.Hom.hom r.retract))

/-- The transpose of a map between finite projectives with superfluous kernel is projective
exactly when it is zero. -/
@[simp]
theorem projective_auslanderReitenTranspose_iff_subsingleton
    (h : IsSuperfluous (LinearMap.ker p₁)) :
    Module.Projective Aᵐᵒᵖ (AuslanderReitenTranspose p₁) ↔
      Subsingleton (AuslanderReitenTranspose p₁) := by
  constructor
  · intro hQ
    let := hQ
    exact h.subsingleton_of_retract_auslanderReitenTranspose LinearMap.id LinearMap.id
      (LinearMap.id_comp _)
  · intro hQ
    let := hQ
    infer_instance

end TauCeti.IsSuperfluous
