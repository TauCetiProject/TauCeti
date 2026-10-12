/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SemiDirect
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Nilpotent
public import TauCeti.Algebra.Lie.OfAssociative

/-!
# Representations of split extensions on enveloping quotients

Let `ψ : H →ₗ⁅R⁆ LieDerivation R S S` define a split Lie extension, and let `J` be a two-sided
ideal of `U(S)` preserved by the lifted derivations. On `U(S)/J`, the element `(s, h)` acts as
left multiplication by the class of `ι(s)` plus the derivation induced by `ψ(h)`. This gives a
representation of `S ⋊⁅ψ⁆ H`. Evaluating at the unit shows that its kernel on `S` consists
exactly of those `s` with `ι(s) ∈ J`.

In particular, if `J` is contained in the kernel of the enveloping extension of a starting
representation `σ` of `S`, the new representation detects every direction detected by `σ`.
When the quotient is finite dimensional, this is the kernel control needed to extend
finite-dimensional representations through split ideal extensions. If `ψ(h)` is locally nilpotent on
`S` and the quotient is finitely generated over `R`, the element `(0, h)` also acts nilpotently on
the quotient.

The construction uses `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivationHom` to lift the
acting derivations and `TauCeti.derivationQuotientHom` to descend them to the quotient.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  Proposition E.5, for the multiplication-plus-derivation construction.
* S. Asgarli, [*Ado's Theorem*](https://personal.math.ubc.ca/~reichst/Ado%27s-Theorem.pdf),
  Proposition 2, for the split-extension argument and its kernel control.
-/

public section

namespace TauCeti

open LieAlgebra
open TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (S : Type v) {H : Type w}
  [CommRing R] [LieRing S] [LieAlgebra R S] [LieRing H] [LieAlgebra R H]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R S

variable (ψ : H →ₗ⁅R⁆ LieDerivation R S S)
  (J : Ideal (_root_.UniversalEnvelopingAlgebra R S)) [J.IsTwoSided]
  (hJ : ∀ h : H, envelopingDerivation R S (ψ h) ∈
    stableDerivations R (J.restrictScalars R))

/-- The action of `H` by derivations on a stable two-sided enveloping quotient. -/
noncomputable def envelopingQuotientDerivation : H →ₗ⁅R⁆ derivationLieAlgebra R (U ⧸ J) :=
  (derivationQuotientHom R J).comp
    { ((envelopingDerivationHom R S).comp ψ).toLinearMap.codRestrict
        (stableDerivations R (J.restrictScalars R)).toSubmodule
        (fun h ↦ by simpa only [LieHom.coe_toLinearMap, LieHom.comp_apply,
          envelopingDerivationHom_apply, LieSubalgebra.mem_toSubmodule] using hJ h)
      with
      map_lie' := fun {h k} ↦ Subtype.ext (((envelopingDerivationHom R S).comp ψ).map_lie h k) }

/-- Descended derivations act on a class by differentiating a representative. -/
@[simp]
theorem envelopingQuotientDerivation_apply_mk (h : H) (a : U) :
    (envelopingQuotientDerivation R S ψ J hJ h : Module.End R (U ⧸ J)) (Ideal.Quotient.mk J a) =
      Ideal.Quotient.mk J ((envelopingDerivation R S (ψ h) : Module.End R U) a) := by
  unfold envelopingQuotientDerivation
  rw [LieHom.comp_apply, derivationQuotientHom_apply_mk]
  -- The codomain restriction changes only the proof of stability, so its two subtype
  -- coercions have the same underlying endomorphism as the lifted homomorphism.
  change Ideal.Quotient.mk J
    ((((envelopingDerivationHom R S).comp ψ) h : Module.End R U) a) = _
  rw [LieHom.comp_apply, envelopingDerivationHom_apply]

/-- On a canonical Lie generator the quotient derivation is the original Lie derivation. -/
theorem envelopingQuotientDerivation_apply_ι (h : H) (s : S) :
    (envelopingQuotientDerivation R S ψ J hJ h : Module.End R (U ⧸ J))
        (Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R s)) =
      Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R (ψ h s)) := by
  rw [envelopingQuotientDerivation_apply_mk, envelopingDerivation_ι]

/-- The representation of a split extension on a stable enveloping quotient, by left
multiplication for `S` and descended derivations for `H`. -/
noncomputable def envelopingQuotientRep : (S ⋊⁅ψ⁆ H) →ₗ⁅R⁆ Module.End R (U ⧸ J) :=
  let q : S →ₗ⁅R⁆ (U ⧸ J) :=
    ((Ideal.Quotient.mkₐ R J : U →ₐ[R] U ⧸ J) : U →ₗ⁅R⁆ U ⧸ J).comp
      (_root_.UniversalEnvelopingAlgebra.ι R)
  let δ := envelopingQuotientDerivation R S ψ J hJ
  { (LieHom.leftRegularRep q).toLinearMap.comp (SemiDirectSum.projl ψ) +
      ((derivationLieAlgebra R (U ⧸ J)).incl.comp δ).toLinearMap.comp
        (SemiDirectSum.projr ψ).toLinearMap with
    map_lie' := by
      intro x y
      apply LinearMap.ext
      intro a
      have hδ (h : H) (s : S) : (δ h : Module.End R (U ⧸ J)) (q s) = q (ψ h s) :=
        envelopingQuotientDerivation_apply_ι R S ψ J hJ h s
      -- The structure extension presents the sum through `LinearMap.toFun`; expose the
      -- two component endomorphisms before using their public evaluation lemmas.
      change (q.leftRegularRep ⁅x, y⁆.left + (δ ⁅x, y⁆.right : Module.End R (U ⧸ J))) a =
        ⁅q.leftRegularRep x.left + (δ x.right : Module.End R (U ⧸ J)),
          q.leftRegularRep y.left + (δ y.right : Module.End R (U ⧸ J))⁆ a
      simp only [SemiDirectSum.lie_eq_mk, LinearMap.add_apply,
        LieHom.leftRegularRep_apply, map_sub, map_add, LieHom.map_lie,
        LieSubalgebra.coe_bracket, Ring.lie_def,
        Module.End.mul_apply, LinearMap.sub_apply, derivationLieAlgebra.leibniz, hδ]
      abel }

/-- The multiplication-plus-derivation formula for the split extension action. -/
@[simp]
theorem envelopingQuotientRep_apply (x : S ⋊⁅ψ⁆ H) (a : U ⧸ J) :
    envelopingQuotientRep R S ψ J hJ x a =
      Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R x.left) * a +
        (envelopingQuotientDerivation R S ψ J hJ x.right : Module.End R (U ⧸ J)) a := by
  unfold envelopingQuotientRep
  -- Evaluation of the structure extension is evaluation of the sum of its two linear maps.
  change
    LieHom.leftRegularRep
        (((Ideal.Quotient.mkₐ R J : U →ₐ[R] U ⧸ J) : U →ₗ⁅R⁆ U ⧸ J).comp
          (_root_.UniversalEnvelopingAlgebra.ι R)) x.left a +
      (envelopingQuotientDerivation R S ψ J hJ x.right : Module.End R _) a = _
  simp only [LieHom.leftRegularRep_apply, LieHom.comp_apply, AlgHom.coe_toLieHom,
    Ideal.Quotient.mkₐ_eq_mk]

/-- On the ideal summand, the extension acts by left multiplication by the canonical image. -/
@[simp]
theorem envelopingQuotientRep_mk_zero (s : S) :
    envelopingQuotientRep R S ψ J hJ ⟨s, 0⟩ =
      LinearMap.mulLeft R (Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R s)) := by
  apply LinearMap.ext
  intro a
  simp only [envelopingQuotientRep_apply, map_zero,
    ZeroMemClass.coe_zero, LinearMap.zero_apply, add_zero, LinearMap.mulLeft_apply]

/-- On the complementary summand, the extension acts by the descended enveloping derivation. -/
@[simp]
theorem envelopingQuotientRep_zero_mk (h : H) :
    envelopingQuotientRep R S ψ J hJ ⟨0, h⟩ =
      (envelopingQuotientDerivation R S ψ J hJ h : Module.End R (U ⧸ J)) := by
  apply LinearMap.ext
  intro a
  simp only [envelopingQuotientRep_apply, map_zero, zero_mul, zero_add]

/-- Refining the enveloping kernel of a representation preserves all directions it detects:
the kernel of the new action restricted to `S` lies in the starting representation's kernel. -/
theorem ker_envelopingQuotientRep_comp_inl_le {V : Type*} [AddCommGroup V] [Module R V]
    (σ : S →ₗ⁅R⁆ Module.End R V)
    (hker : J ≤ RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R σ)) :
    ((envelopingQuotientRep R S ψ J hJ).comp (SemiDirectSum.inl ψ)).ker ≤ σ.ker := by
  intro s hs
  rw [LieHom.mem_ker, LieHom.comp_apply,
    SemiDirectSum.inl_eq_mk, envelopingQuotientRep_mk_zero,
    LinearMap.mulLeft_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hs
  have := hker hs
  rw [LieHom.mem_ker]
  simpa only [RingHom.mem_ker, _root_.UniversalEnvelopingAlgebra.lift_ι_apply] using this

/-- A complementary element whose derivation on the ideal is locally nilpotent acts nilpotently on
any stable enveloping quotient that is finitely generated over the coefficient ring. -/
theorem isNilpotent_envelopingQuotientRep_inr [Module.Finite R (U ⧸ J)] (h : H)
    (hψ : ∀ s : S, ∃ n : ℕ, ((ψ h).toLinearMap ^ n) s = 0) :
    IsNilpotent (envelopingQuotientRep R S ψ J hJ (SemiDirectSum.inr ψ h)) := by
  rw [SemiDirectSum.inr_eq_mk, envelopingQuotientRep_zero_mk]
  have hδ : (envelopingQuotientDerivation R S ψ J hJ h : Module.End R (U ⧸ J)) =
      (derivationQuotientHom R J ⟨envelopingDerivation R S (ψ h), hJ h⟩ :
        Module.End R (U ⧸ J)) := by
    apply LinearMap.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [envelopingQuotientDerivation_apply_mk, derivationQuotientHom_apply_mk]
  rw [hδ]
  exact isNilpotent_envelopingDerivation_quotient R S (ψ h) hψ J (hJ h)

end TauCeti
