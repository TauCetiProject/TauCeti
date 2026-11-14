/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Complex
public import TauCeti.Analysis.Normed.Algebra.VirtualDiagonal
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Normed.Module.Dual.Bidual
import TauCeti.Analysis.Normed.Module.Dual.ClusterPt
import TauCeti.Analysis.Normed.Module.Dual.Goldstine
import TauCeti.Analysis.Normed.Operator.Restrict
import TauCeti.Analysis.Normed.Ring.ApproximateUnit

/-!
# Amenable Banach algebras and Johnson's diagonal characterizations

A normed algebra `A` over `𝕜` is *amenable*, in the sense of B. E. Johnson, if for every Banach
`A`-bimodule `E` in the universe of `A` every bounded derivation `D : A → E*` into the dual
bimodule is inner. Here a bimodule is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`,
with `a · x = L a x` and `x · a = R a x`, and the dual `E*` carries the dual actions of
`TauCeti.Analysis.Normed.Module.Dual.Bimodule`: the left action is `dualAction R` and the right
action is `dualAction L`. A bounded derivation is a bounded operator `D` with
`D (a * b) = a · D b + D a · b`, and it is inner when `D a = a · φ - φ · a` for some `φ ∈ E*`.
Equivalently, the first bounded Hochschild cohomology `H¹(A, E*)` vanishes for every such `E`.

This file proves Johnson's equivalent characterizations of amenability:

1. **Sufficiency of virtual and approximate diagonals.** Over any complete nontrivially normed
   field `𝕜`, if a Banach algebra `A` has a virtual diagonal `M ∈ (A ⊗̂π A)**`, then every bounded
   derivation `D : A →L[𝕜] E*` into the dual of a normed `A`-bimodule `E` (in any universe, without
   requiring completeness of `E` or essentiality of the actions) is inner. Over a proper scalar
   field, a bounded approximate diagonal gives a virtual diagonal by Banach–Alaoglu and hence also
   implies amenability.
2. **Bounded approximate identities from amenability.** Over `ℝ` or `ℂ`, applying amenability to
   the canonical inclusion `J_A : A →L[𝕜] A**` for the one-sided actions `(mul, 0)` and
   `(0, mul.flip)` produces elements in `A**` that Goldstine's theorem approximates in norm on
   finite subsets, yielding bounded left and right approximate identities and hence a bounded
   two-sided approximate identity by Dixon's combination.
3. **Necessity of virtual and approximate diagonals.** Over `ℝ` or `ℂ`, given a bounded two-sided
   approximate identity `(eᵢ)` of an amenable Banach algebra `A`, a weak-star cluster point `E₀` of
   `eᵢ ⊗ eᵢ` in `(A ⊗̂π A)**` satisfies `a · Δ** E₀ = J_A a = Δ** E₀ · a`, so `a ↦ a · E₀ - E₀ · a`
   is a bounded derivation with values in `ker Δ**`. By Cohen–Hewitt factorization `Δ = mul' 𝕜 A`
   is surjective, so `(ker Δ).subtypeL**` identifies `(ker Δ)**` isometrically with `ker Δ**`.
   Innerness on `(ker Δ)**` supplies `N ∈ ker Δ**` such that `M = E₀ - N` is a virtual diagonal,
   and Goldstine's theorem turns `M` into a bounded approximate diagonal.

Consequently, for a Banach algebra `A` over `ℝ` or `ℂ`, amenability is equivalent to the existence
of a virtual diagonal and to the existence of a bounded approximate diagonal, and implies innerness
of bounded derivations into `E*` (hence `H¹(A, E*) = 0`) for normed bimodules `E` in arbitrary
universes.

## Main definitions

* `TauCeti.IsAmenable`: amenability of a normed algebra.

## Main results

* `TauCeti.IsVirtualDiagonal.exists_eq_dualAction_sub_dualAction` and
  `TauCeti.IsApproximateDiagonal.exists_eq_dualAction_sub_dualAction`: virtual diagonals (over a
  complete field) and bounded approximate diagonals (over a proper field) force all bounded
  derivations into dual bimodules to be inner.
* `TauCeti.isAmenable_iff_forall_subsingleton_hochschildBimoduleCohomology_one`: amenability is
  the vanishing of `H¹(A, E*)` for all Banach bimodules `E` in the universe of `A`.
* `TauCeti.IsVirtualDiagonal.isAmenable` and `TauCeti.IsApproximateDiagonal.isAmenable`:
  sufficiency of virtual and bounded approximate diagonals for amenability.
* `TauCeti.IsAmenable.exists_isApproximateUnit`: every amenable Banach algebra over `ℝ` or `ℂ` has
  a bounded two-sided approximate identity.
* `TauCeti.IsAmenable.exists_isVirtualDiagonal` and
  `TauCeti.IsAmenable.exists_isApproximateDiagonal`: every amenable Banach algebra over `ℝ` or `ℂ`
  has a virtual diagonal and a bounded approximate diagonal.
* `TauCeti.isAmenable_iff_exists_isVirtualDiagonal` and
  `TauCeti.isAmenable_iff_exists_isApproximateDiagonal`: Johnson's diagonal characterizations of
  amenable Banach algebras over `ℝ` or `ℂ`.
* `TauCeti.IsAmenable.exists_eq_dualAction_sub_dualAction'` and
  `TauCeti.IsAmenable.subsingleton_hochschildBimoduleCohomology_one`: universe-polymorphic
  innerness and `H¹(A, E*) = 0` for amenable Banach algebras over `ℝ` or `ℂ`.
* `TauCeti.isAmenable_self` and `TauCeti.isAmenable_of_subsingleton`: the base field and the zero
  algebra are amenable.

## Implementation notes

Two technical devices avoid both an essential-bimodule reduction and any universe restriction
between `A : Type u` and `𝕜 : Type v`:

* For sufficiency, pushing the operator `Φ : A ⊗̂π A →L[𝕜] E*` induced by `(a, b) ↦ a · D b`
  through a virtual diagonal `M` directly produces functionals `φ`, `ψ`, `ρ ∈ E*` with
  `D a = a · φ - φ · a + ψ · a`, `a · ρ = a · ψ`, and `ρ · a = 0`, so `φ + ρ - ψ` witnesses
  innerness without assuming `E` is essential.
* For necessity, `IsAmenable 𝕜 A` quantifies over Banach bimodules in `Type u`, whereas for
  `X : Type u` and `𝕜 : Type v` the dual `X* = X →L[𝕜] 𝕜` lies in `Type (max u v)`. When `A` is
  nontrivial, Hahn–Banach supplies `e : A` and `π ∈ A*` with `π e = 1`, exhibiting `X*` as a
  bounded bimodule retract of the Banach bimodule `X →L[𝕜] A : Type u`; when `A` is subsingleton,
  every derivation is zero. Thus `IsAmenable 𝕜 A` applies directly to derivations into `A**` and
  `(ker Δ)**` without tying `u` and `v`.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.1 and §2.2, Theorem 2.2.4.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§2.8–2.9.
-/

public section

noncomputable section

universe u v

open Filter NormedSpace Topology ContinuousLinearMap

namespace TauCeti

open CompletedProjectiveTensor

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

section Derivation

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {L R : A →L[𝕜] E →L[𝕜] E}

/-- The bounded operator `A ⊗̂π A → E*` induced by the bounded bilinear map `(a, b) ↦ a · D b`. -/
private abbrev leftDerivationLift [CompleteSpace 𝕜] (R : A →L[𝕜] E →L[𝕜] E)
    (D : A →L[𝕜] StrongDual 𝕜 E) : CompletedProjectiveTensor 𝕜 A A →L[𝕜] StrongDual 𝕜 E :=
  liftIsometry 𝕜 A A (StrongDual 𝕜 E) ((compL 𝕜 E E 𝕜).bilinearComp D R).flip

/-- The commutator of `Φ m` with `a`, where `Φ` is induced by `(a, b) ↦ a · D b`:
`a · Φ m - Φ m · a = Φ (a · m - m · a) + Δ m · D a`. -/
private theorem dualAction_leftDerivationLift_sub [CompleteSpace 𝕜]
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (a : A) (m : CompletedProjectiveTensor 𝕜 A A) :
    dualAction R a (leftDerivationLift R D m) - dualAction L a (leftDerivationLift R D m) =
      leftDerivationLift R D (mulLeft 𝕜 A a m - mulRight 𝕜 A a m) +
        dualAction R (mul' 𝕜 A m) (D a) := by
  have key : (dualAction R a - dualAction L a) ∘L leftDerivationLift R D =
      leftDerivationLift R D ∘L (mulLeft 𝕜 A a - mulRight 𝕜 A a) +
        (compL 𝕜 E E 𝕜 (D a) ∘L R) ∘L mul' 𝕜 A := by
    refine continuousLinearMap_ext fun x y ↦ ?_
    ext z
    simp [ProjectiveTensor.liftIsometry_apply_tmul, hD, hR, hLR]
    ring
  ext x
  simpa using congr($key m x)

/-- If a Banach algebra `A` over a complete scalar field has a virtual diagonal `M`, then every
bounded derivation `D` of `A` into the dual `E*` of a normed `A`-bimodule `E` is inner:
`D a = a · φ - φ · a` for some `φ ∈ E*`, where `E*` has left action `dualAction R` and right action
`dualAction L`. Neither `A` nor the actions need to be unital or contractive, and `E` need not be
complete or essential. -/
theorem IsVirtualDiagonal.exists_eq_dualAction_sub_dualAction [CompleteSpace 𝕜]
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  set Φ := leftDerivationLift R D
  set J := inclusionInDoubleDual 𝕜 E
  let φ : StrongDual 𝕜 E := M ∘L precomp 𝕜 Φ ∘L J
  let ψ : StrongDual 𝕜 E := M ∘L precomp 𝕜 (D ∘L mul' 𝕜 A) ∘L J
  let ρ : StrongDual 𝕜 E := M ∘L precomp 𝕜 ((dualAction R).flip ψ ∘L mul' 𝕜 A) ∘L J
  -- Pushing `a · Φ m - Φ m · a = Φ (a · m - m · a) + D (Δ m * a) - D (Δ m) · a` through `M`
  -- gives `D a = a · φ - φ · a + ψ · a`.
  have hDφψ (a : A) (x : E) : D a x = φ (R a x) - φ (L a x) + ψ (L a x) := by
    have hkey : (J (R a x)).comp Φ - (J (L a x)).comp Φ =
        ((J x).comp Φ).comp (mulLeft 𝕜 A a) - ((J x).comp Φ).comp (mulRight 𝕜 A a) +
          (((J x).comp D).comp ((ContinuousLinearMap.mul 𝕜 A).flip a)).comp (mul' 𝕜 A) -
            (J (L a x)).comp (D ∘L mul' 𝕜 A) := by
      refine ContinuousLinearMap.ext fun m ↦ ?_
      have hm := congr($(dualAction_leftDerivationLift_sub hR hLR hD a m) x)
      have hDm := congr($(hD (mul' 𝕜 A m) a) x)
      simp only [Φ, J, map_sub, sub_apply, add_apply, comp_apply, dual_def, flip_apply,
        mul_apply', dualAction_apply_apply] at hm hDm ⊢
      linear_combination hm - hDm
    have hMkey := congrArg M hkey
    simp only [map_sub, map_add, hM.apply_comp_mulLeft_eq_mulRight, sub_self, zero_add,
      hM.apply_comp_mul_flip_comp_mul', J, comp_apply, dual_def] at hMkey
    simp only [φ, ψ, J, comp_apply, precomp_apply]
    linear_combination -hMkey
  -- Since `D` and the inner derivation of `φ` are derivations, `ψ (b · x · a) = 0`.
  have hψLR (a b : A) (x : E) : ψ (R a (L b x)) = 0 := by
    have := congr($(hD a b) x)
    simp only [dualAction_apply_apply, add_apply, hDφψ, hL, hR, hLR] at this
    linear_combination -this
  -- Hence `a · ρ = a · ψ` and `ρ · a = 0`, so `φ + ρ - ψ` implements `D`.
  have hρR (a : A) (x : E) : ρ (R a x) = ψ (R a x) := by
    have hEq : (J (R a x)).comp ((dualAction R).flip ψ ∘L mul' 𝕜 A) =
        ((ψ.comp (R.flip x)).comp (ContinuousLinearMap.mul 𝕜 A a)).comp (mul' 𝕜 A) :=
      ContinuousLinearMap.ext fun m ↦ by simp [J, hR]
    simpa only [ρ, comp_apply, precomp_apply, flip_apply, hEq] using
      hM.apply_comp_mul_comp_mul' a (ψ.comp (R.flip x))
  have hρL (a : A) (x : E) : ρ (L a x) = 0 := by
    have hEq : (J (L a x)).comp ((dualAction R).flip ψ) = 0 := by
      ext b
      simp [J, hψLR]
    simp [ρ, ← comp_assoc, hEq]
  refine ⟨φ + ρ - ψ, fun a ↦ ?_⟩
  ext x
  simp only [dualAction_apply_apply, sub_apply, add_apply, hDφψ, hρR, hρL]
  ring

/-- If a Banach algebra `A` over a proper scalar field has a bounded approximate diagonal, then
every bounded derivation `D` of `A` into the dual `E*` of a normed `A`-bimodule `E` is inner:
`D a = a · φ - φ · a` for some `φ ∈ E*`, where `E*` has left action `dualAction R` and right action
`dualAction L`. Neither `A` nor the actions need to be unital or contractive, and `E` need not be
complete or essential. -/
theorem IsApproximateDiagonal.exists_eq_dualAction_sub_dualAction [ProperSpace 𝕜]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (h : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  obtain ⟨M, hM, -⟩ := h.exists_isVirtualDiagonal hC
  exact hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

end Derivation

section Amenable

variable (𝕜 : Type v) (A : Type u) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- A normed algebra `A` over `𝕜` is *amenable* if, for every Banach `A`-bimodule `E` in the
universe of `A`, every bounded derivation of `A` into the dual bimodule `E*` is inner.

The bimodule structure is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`,
`a · x = L a x` and `x · a = R a x`, which need not be unital or contractive. The dual `E*` has
left action `dualAction R` and right action `dualAction L`. A bounded derivation is a bounded
operator `D : A →L[𝕜] E*` with `D (a * b) = a · D b + D a · b`, and it is inner when
`D a = a · φ - φ · a` for some `φ ∈ E*`. -/
def IsAmenable : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (L R : A →L[𝕜] E →L[𝕜] E), (∀ a b x, L (a * b) x = L a (L b x)) →
      (∀ a b x, R (a * b) x = R b (R a x)) → (∀ a b x, L a (R b x) = R b (L a x)) →
      ∀ D : A →L[𝕜] StrongDual 𝕜 E,
        (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
          ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ

/-- A normed algebra is amenable exactly when the first bounded Hochschild cohomology
`H¹(A, E*)` vanishes for every Banach `A`-bimodule `E` in the universe of `A`. -/
theorem isAmenable_iff_forall_subsingleton_hochschildBimoduleCohomology_one :
    IsAmenable 𝕜 A ↔ ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      (L R : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b x, L (a * b) x = L a (L b x))
      (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x)),
        Subsingleton (hochschildBimoduleCohomology (dualAction R) (dualAction L)
          (dualAction_mul_apply_of_right hR) (dualAction_mul_apply_of_left hL)
          (dualAction_apply_dualAction_apply_comm hLR) 1) := by
  constructor
  · intro h E _ _ _ L R hL hR hLR
    exact (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).2
      (h E L R hL hR hLR)
  · intro h E _ _ _ L R hL hR hLR
    exact (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).1
      (h E L R hL hR hLR)

variable {𝕜 A}

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- The characteristic property of amenability: for every Banach `A`-bimodule `E` in the universe
of `A`, every bounded derivation `D : A → E*` is inner. -/
theorem isAmenable_def : IsAmenable 𝕜 A ↔
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      (L R : A →L[𝕜] E →L[𝕜] E), (∀ a b x, L (a * b) x = L a (L b x)) →
        (∀ a b x, R (a * b) x = R b (R a x)) → (∀ a b x, L a (R b x) = R b (L a x)) →
        ∀ D : A →L[𝕜] StrongDual 𝕜 E,
          (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
            ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  Iff.rfl

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- In an amenable normed algebra `A`, every bounded derivation `D` of `A` into the dual `E*` of a
Banach `A`-bimodule `E` in the universe of `A` is inner: `D a = a · φ - φ · a` for some
`φ ∈ E*`, where `E*` has left action `dualAction R` and right action `dualAction L`. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction (h : IsAmenable 𝕜 A) {E : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  h E L R hL hR hLR D hD

/-- A Banach algebra over a complete scalar field with a virtual diagonal is amenable. -/
theorem IsVirtualDiagonal.isAmenable [CompleteSpace 𝕜] [CompleteSpace A]
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ hL hR hLR D hD ↦ hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

/-- A Banach algebra over a proper scalar field with a bounded approximate diagonal is amenable. -/
theorem IsApproximateDiagonal.isAmenable [ProperSpace 𝕜] [CompleteSpace A]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (h : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ hL hR hLR D hD ↦ h.exists_eq_dualAction_sub_dualAction hC hL hR hLR D hD

variable (𝕜 A) in
omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- Every subsingleton normed algebra (in particular, the zero algebra) is amenable. -/
theorem isAmenable_of_subsingleton [Subsingleton A] : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ _ _ _ _ _ ↦ ⟨0, fun a ↦ by simp [Subsingleton.elim a 0]⟩

variable (𝕜) in
/-- A complete base field is amenable over itself. -/
theorem isAmenable_self [CompleteSpace 𝕜] : IsAmenable 𝕜 𝕜 :=
  (isVirtualDiagonal_inclusionInDoubleDual_one_tmul_one 𝕜).isAmenable

end Amenable

section DiagonalCharacterization

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- In an amenable Banach algebra `A : Type u` over `𝕜 : Type v` (`ℝ` or `ℂ`), every bounded
derivation into the bidual `X**` of a normed `A`-bimodule `X : Type u` is inner, with no
completeness hypothesis on `X` and no universe constraint between `u` and `v`. -/
private theorem IsAmenable.exists_eq_bidual_dualAction_sub_dualAction
    (h : IsAmenable 𝕜 A) {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {L R : A →L[𝕜] X →L[𝕜] X}
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X))
    (hD : ∀ a b, D (a * b) =
      dualAction (dualAction L) a (D b) + dualAction (dualAction R) b (D a)) :
    ∃ Φ : StrongDual 𝕜 (StrongDual 𝕜 X),
      ∀ a, D a = dualAction (dualAction L) a Φ - dualAction (dualAction R) a Φ := by
  by_cases hA : Subsingleton A
  · exact ⟨0, fun a ↦ by simp [hA.elim a 0]⟩
  -- When `A` is nontrivial, a functional `π ∈ A*` with `π e = 1` exhibits `X* : Type (max u v)`
  -- as a bounded bimodule retract of the Banach bimodule `X →L[𝕜] A : Type u`.
  rw [not_subsingleton_iff_nontrivial] at hA
  obtain ⟨e, he⟩ := exists_ne (0 : A)
  obtain ⟨π, hπe⟩ := SeparatingDual.exists_eq_one (R := 𝕜) he
  let L₀ : A →L[𝕜] (X →L[𝕜] A) →L[𝕜] (X →L[𝕜] A) := (compL 𝕜 X X A).flip ∘L R
  let R₀ : A →L[𝕜] (X →L[𝕜] A) →L[𝕜] (X →L[𝕜] A) := (compL 𝕜 X X A).flip ∘L L
  have hL₀ (a b : A) (T : X →L[𝕜] A) : L₀ (a * b) T = L₀ a (L₀ b T) := by ext x; simp [L₀, hR]
  have hR₀ (a b : A) (T : X →L[𝕜] A) : R₀ (a * b) T = R₀ b (R₀ a T) := by ext x; simp [R₀, hL]
  have hLR₀ (a b : A) (T : X →L[𝕜] A) : L₀ a (R₀ b T) = R₀ b (L₀ a T) := by
    ext x; simp [L₀, R₀, hLR]
  let p : (X →L[𝕜] A) →L[𝕜] StrongDual 𝕜 X := compL 𝕜 X A 𝕜 π
  let ι : StrongDual 𝕜 X →L[𝕜] (X →L[𝕜] A) :=
    compL 𝕜 X 𝕜 A ((ContinuousLinearMap.id 𝕜 𝕜).smulRight e)
  have hpι (f : StrongDual 𝕜 X) : p (ι f) = f := by ext x; simp [p, ι, hπe]
  have hpL (a : A) (T : X →L[𝕜] A) : p (L₀ a T) = dualAction R a (p T) := by ext x; simp [p, L₀]
  have hpR (a : A) (T : X →L[𝕜] A) : p (R₀ a T) = dualAction L a (p T) := by ext x; simp [p, R₀]
  have hιL (a : A) (f : StrongDual 𝕜 X) : ι (dualAction R a f) = L₀ a (ι f) := by
    ext x; simp [ι, L₀]
  have hιR (a : A) (f : StrongDual 𝕜 X) : ι (dualAction L a f) = R₀ a (ι f) := by
    ext x; simp [ι, R₀]
  let D₀ : A →L[𝕜] StrongDual 𝕜 (X →L[𝕜] A) := precomp 𝕜 p ∘L D
  have hD₀ (a b : A) : D₀ (a * b) = dualAction R₀ a (D₀ b) + dualAction L₀ b (D₀ a) := by
    simp only [D₀, comp_apply, hD, map_add, precomp_dualAction_apply hpR,
      precomp_dualAction_apply hpL]
  obtain ⟨Ψ, hΨ⟩ := h.exists_eq_dualAction_sub_dualAction hL₀ hR₀ hLR₀ D₀ hD₀
  refine ⟨precomp 𝕜 ι Ψ, fun a ↦ ?_⟩
  have hDa : D a = precomp 𝕜 ι (D₀ a) := by ext f; simp [D₀, hpι]
  rw [hDa, hΨ a, map_sub, precomp_dualAction_apply hιR, precomp_dualAction_apply hιL]

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A] in
/-- If `Φ ∈ A**` satisfies `Φ (f ∘ T a) = f a` for all `a : A` and `f ∈ A*`, then there is a proper
filter on `A` bounded by `‖Φ‖` along which `T a e → a` for every `a`. -/
private theorem exists_tendsto_of_forall_apply_comp_eq (T : A →L[𝕜] A →L[𝕜] A)
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 A))
    (hΦ : ∀ (a : A) (f : StrongDual 𝕜 A), Φ (f.comp (T a)) = f a) :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ ‖Φ‖) ∧ ∀ a, Tendsto (T a) l (𝓝 a) := by
  refine (exists_neBot_tendsto_iff_forall_finset_dist_lt (p := fun e : A ↦ ‖e‖ ≤ ‖Φ‖)
    (F := fun a e ↦ T a e) (x := id)).2 fun s ε hε ↦ ?_
  obtain ⟨e, he, happrox⟩ := Φ.exists_norm_le_and_forall_norm_sub_lt
    (fun a : s ↦ T a.1) (fun a : s ↦ a.1) (fun a ↦ hΦ a.1) le_rfl hε
  exact ⟨e, he, fun a ha ↦ by simpa only [dist_eq_norm, id_eq] using happrox ⟨a, ha⟩⟩

/-- Every amenable Banach algebra over `ℝ` or `ℂ` has a bounded right approximate identity. -/
private theorem IsAmenable.exists_tendsto_mul_left (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (a * ·) l (𝓝 a) := by
  -- Apply bidual innerness to `J_A : A →L[𝕜] A**` for the one-sided actions `(mul, 0)`.
  have hD (a b : A) : inclusionInDoubleDual 𝕜 A (a * b) =
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a (inclusionInDoubleDual 𝕜 A b) +
        dualAction (dualAction (0 : A →L[𝕜] A →L[𝕜] A)) b (inclusionInDoubleDual 𝕜 A a) := by
    ext f; simp
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_bidual_dualAction_sub_dualAction
    (fun a b x ↦ mul_assoc a b x) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (inclusionInDoubleDual 𝕜 A) hD
  refine ⟨‖Φ‖, exists_tendsto_of_forall_apply_comp_eq (ContinuousLinearMap.mul 𝕜 A) Φ fun a f ↦ ?_⟩
  have ha := congr($(hΦ a) f)
  simpa only [sub_apply, dualAction_apply_apply, dualAction_apply, comp_apply, precomp_apply,
    zero_apply, comp_zero, map_zero, sub_zero, dual_def] using ha.symm

/-- Every amenable Banach algebra over `ℝ` or `ℂ` has a bounded left approximate identity. -/
private theorem IsAmenable.exists_tendsto_mul_right (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (· * a) l (𝓝 a) := by
  -- Apply bidual innerness to `-J_A : A →L[𝕜] A**` for the one-sided actions `(0, mul.flip)`.
  have hD (a b : A) : (-inclusionInDoubleDual 𝕜 A) (a * b) =
      dualAction (dualAction (0 : A →L[𝕜] A →L[𝕜] A)) a ((-inclusionInDoubleDual 𝕜 A) b) +
        dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) b
          ((-inclusionInDoubleDual 𝕜 A) a) := by
    ext f; simp
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_bidual_dualAction_sub_dualAction
    (fun _ _ _ ↦ by simp) (fun a b x ↦ (mul_assoc x a b).symm) (fun _ _ _ ↦ by simp)
    (-inclusionInDoubleDual 𝕜 A) hD
  refine ⟨‖Φ‖, exists_tendsto_of_forall_apply_comp_eq (ContinuousLinearMap.mul 𝕜 A).flip Φ
    fun a f ↦ ?_⟩
  have ha := congr($(hΦ a) f)
  simpa only [neg_apply, sub_apply, dualAction_apply_apply, dualAction_apply, comp_apply,
    precomp_apply, zero_apply, comp_zero, map_zero, zero_sub, neg_inj, dual_def] using ha.symm

/-- Every amenable Banach algebra over `ℝ` or `ℂ` has a bounded two-sided approximate identity. -/
theorem IsAmenable.exists_isApproximateUnit (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.IsApproximateUnit ∧ ∀ᶠ e in l, ‖e‖ ≤ C := by
  obtain ⟨C, hleft⟩ := h.exists_tendsto_mul_right
  obtain ⟨D, hright⟩ := h.exists_tendsto_mul_left
  exact ⟨C + D + C * D, exists_isApproximateUnit_of_left_of_right hleft hright⟩

/-- If a Banach algebra `A` over `ℝ` or `ℂ` has a bounded two-sided approximate identity, then
there is `E₀ ∈ (A ⊗̂π A)**` satisfying `E₀ (f ∘ mul a ∘ Δ) = f a` and
`E₀ (f ∘ (· * a) ∘ Δ) = f a` for all `a : A` and `f ∈ A*`. -/
private theorem exists_bidual_mul_comp_mul'_eq_of_isApproximateUnit
    {l : Filter A} (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    ∃ E₀ : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      (∀ (a : A) (f : StrongDual 𝕜 A),
        E₀ ((f.comp (ContinuousLinearMap.mul 𝕜 A a)).comp (mul' 𝕜 A)) = f a) ∧
      (∀ (a : A) (f : StrongDual 𝕜 A),
        E₀ ((f.comp ((ContinuousLinearMap.mul 𝕜 A).flip a)).comp (mul' 𝕜 A)) = f a) := by
  -- Take a weak-star cluster point `E₀` of `e ⊗ₜ e` along the bounded approximate identity.
  have := hl.neBot
  obtain ⟨e₀, he₀⟩ := hC.exists
  have hC0 : 0 ≤ C := (norm_nonneg e₀).trans he₀
  have hbdd : l.IsBoundedUnder (· ≤ ·) norm := isBoundedUnder_of_eventually_le hC
  have hsq : ∀ᶠ m in l.map (fun e ↦ tmulL (𝕜 := 𝕜) e e), ‖m‖ ≤ C * C :=
    eventually_map.2 <| hC.mono fun e he ↦ by
      rw [tmulL_apply]
      exact (norm_coe_tmul_le e e).trans (mul_le_mul he he (norm_nonneg e) hC0)
  obtain ⟨E₀, -, hE₀⟩ := hsq.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜)
  refine ⟨E₀, fun a f ↦ ?_, fun a f ↦ ?_⟩
  · have haee : Tendsto (fun e ↦ a * (e * e)) l (𝓝 a) := by
      simpa [sub_mul, mul_assoc] using
        ((tendsto_sub_nhds_zero_iff.2 (hl.tendsto_mul_left a)).zero_mul_isBoundedUnder_le hbdd).add
          (hl.tendsto_mul_left a)
    refine hE₀.apply_eq_of_tendsto_inclusionInDoubleDual _ (tendsto_map'_iff.2 ?_)
    simpa only [Function.comp_def, comp_apply, tmulL_apply, mul'_coe_tmul, mul_apply'] using
      (f.continuous.tendsto a).comp haee
  · have heea : Tendsto (fun e ↦ (e * e) * a) l (𝓝 a) := by
      simpa [mul_sub, mul_assoc] using
        (isBoundedUnder_le_mul_tendsto_zero hbdd
          (tendsto_sub_nhds_zero_iff.2 (hl.tendsto_mul_right a))).add (hl.tendsto_mul_right a)
    refine hE₀.apply_eq_of_tendsto_inclusionInDoubleDual _ (tendsto_map'_iff.2 ?_)
    simpa only [Function.comp_def, comp_apply, tmulL_apply, mul'_coe_tmul, flip_apply,
      mul_apply'] using (f.continuous.tendsto a).comp heea

omit [CompleteSpace A] in
/-- The inner derivation `a ↦ a · E₀ - E₀ · a` of any `E₀ ∈ (A ⊗̂π A)**` satisfies the derivation
identity for the bidual outer actions. -/
private theorem commutatorDerivation_mulLeft_mulRight_mul
    (E₀ : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))) (a b : A) :
    ((dualAction (dualAction (mulLeft 𝕜 A))).flip E₀ -
      (dualAction (dualAction (mulRight 𝕜 A))).flip E₀) (a * b) =
      dualAction (dualAction (mulLeft 𝕜 A)) a
        (((dualAction (dualAction (mulLeft 𝕜 A))).flip E₀ -
          (dualAction (dualAction (mulRight 𝕜 A))).flip E₀) b) +
        dualAction (dualAction (mulRight 𝕜 A)) b
          (((dualAction (dualAction (mulLeft 𝕜 A))).flip E₀ -
            (dualAction (dualAction (mulRight 𝕜 A))).flip E₀) a) := by
  ext φ
  simp only [sub_apply, add_apply, flip_apply, dualAction_apply_apply,
    dualAction_mul_apply_of_left (mulLeft_mul_apply (𝕜 := 𝕜) (A := A)),
    dualAction_mul_apply_of_right (mulRight_mul_apply (𝕜 := 𝕜) (A := A)),
    dualAction_apply_dualAction_apply_comm (mulLeft_mulRight_apply_comm (𝕜 := 𝕜) (A := A)) b a φ]
  ring

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A] in
/-- Any action intertwined by a linear operator `T` with a linear action on the codomain preserves
`ker T`. -/
private theorem mem_ker_of_intertwine {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {T : X →L[𝕜] Y}
    {M : A →L[𝕜] X →L[𝕜] X} {N : A →L[𝕜] Y →L[𝕜] Y} (hTM : ∀ a x, T (M a x) = N a (T x))
    (a : A) (x : X) (hx : x ∈ T.ker) : M a x ∈ T.ker := by
  simp only [LinearMap.mem_ker, coe_coe] at hx ⊢
  rw [hTM, hx, map_zero]

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- In an amenable Banach algebra `A` over `ℝ` or `ℂ`, if `T : X →L[𝕜] Y` is a closed-range
operator between Banach spaces in `Type u` whose kernel is invariant under bounded bimodule actions
`L` and `R` on `X`, then every bounded derivation `D₀ : A →L[𝕜] X**` taking values in `ker T**` is
implemented by an element `N ∈ ker T**`. -/
private theorem IsAmenable.exists_mem_ker_precomp_precomp_eq_dualAction_sub
    (h : IsAmenable 𝕜 A) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    {T : X →L[𝕜] Y} (hT : IsClosed (T.range : Set Y))
    {L R : A →L[𝕜] X →L[𝕜] X}
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (hKL : ∀ a x, x ∈ T.ker → L a x ∈ T.ker)
    (hKR : ∀ a x, x ∈ T.ker → R a x ∈ T.ker)
    (D₀ : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X))
    (hD₀ : ∀ a b, D₀ (a * b) =
      dualAction (dualAction L) a (D₀ b) + dualAction (dualAction R) b (D₀ a))
    (hD₀_ker : ∀ a, D₀ a ∈
      (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) :
        StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 Y)).ker) :
    ∃ N : StrongDual 𝕜 (StrongDual 𝕜 X),
      N ∈ (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) :
          StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 Y)).ker ∧
      ∀ a, D₀ a = dualAction (dualAction L) a N - dualAction (dualAction R) a N := by
  -- Phase 1: restrict the bimodule actions `L` and `R` to the invariant submodule `ker T`.
  let LK := L.restrictAction T.ker hKL
  let RK := R.restrictAction T.ker hKR
  have hLK (a b : A) (x : T.ker) : LK (a * b) x = LK a (LK b x) := by ext; simp [LK, hL]
  have hRK (a b : A) (x : T.ker) : RK (a * b) x = RK b (RK a x) := by ext; simp [RK, hR]
  have hLRK (a b : A) (x : T.ker) : LK a (RK b x) = RK b (LK a x) := by ext; simp [LK, RK, hLR]
  -- Phase 2: transport `D₀` across `(ker T)** ≃ₗᵢ ker T**` to a derivation into `(ker T)**`.
  let T₂ : StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 Y) :=
    precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X)
  let DK : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 T.ker) :=
    (T.bidualKerEquivKerPrecompPrecomp hT).symm.toLinearIsometry.toContinuousLinearMap ∘L
      D₀.codRestrict T₂.ker hD₀_ker
  have hDK_coe (a : A) : precomp 𝕜 (precomp 𝕜 T.ker.subtypeL) (DK a) = D₀ a := by
    rw [← T.coe_bidualKerEquivKerPrecompPrecomp hT]
    simp [DK]
  have hSL := precomp_dualAction_apply (T := T.ker.subtypeL) (M := LK) (N := L)
    fun a x ↦ by simp [LK]
  have hSR := precomp_dualAction_apply (T := T.ker.subtypeL) (M := RK) (N := R)
    fun a x ↦ by simp [RK]
  have hDK (a b : A) :
      DK (a * b) = dualAction (dualAction LK) a (DK b) + dualAction (dualAction RK) b (DK a) := by
    apply T.ker.bidualEquivDoubleAnnihilator.injective
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add, T.ker.coe_bidualEquivDoubleAnnihilator,
      precomp_dualAction_apply hSL, precomp_dualAction_apply hSR, hDK_coe]
    exact hD₀ a b
  -- Phase 3: apply bidual innerness on `ker T` and push the witness back into `ker T**`.
  obtain ⟨N₀, hN₀⟩ := h.exists_eq_bidual_dualAction_sub_dualAction hLK hRK hLRK DK hDK
  refine ⟨(T.bidualKerEquivKerPrecompPrecomp hT N₀ : StrongDual 𝕜 (StrongDual 𝕜 X)),
    (T.bidualKerEquivKerPrecompPrecomp hT N₀).2, fun a ↦ ?_⟩
  rw [T.coe_bidualKerEquivKerPrecompPrecomp hT, ← precomp_dualAction_apply hSL,
    ← precomp_dualAction_apply hSR, ← map_sub, ← hN₀ a, hDK_coe]

/-- In an amenable Banach algebra `A` over `ℝ` or `ℂ` with surjective multiplication map
`Δ = mul' 𝕜 A`, if `E₀ ∈ (A ⊗̂π A)**` satisfies `E₀ (f ∘ Δ ∘ mulLeft a) = E₀ (f ∘ Δ ∘ mulRight a)`
for all `a : A` and `f ∈ A*`, then there is `N ∈ (A ⊗̂π A)**` with `Δ** N = 0` and the same outer
commutator as `E₀`. -/
private theorem IsAmenable.exists_ker_mul'_eq_commutator
    (h : IsAmenable 𝕜 A) (hsurj : Function.Surjective (mul' 𝕜 A))
    (E₀ : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)))
    (hE₀ : ∀ (a : A) (f : StrongDual 𝕜 A),
      E₀ ((f.comp (mul' 𝕜 A)).comp (mulLeft 𝕜 A a)) =
        E₀ ((f.comp (mul' 𝕜 A)).comp (mulRight 𝕜 A a))) :
    ∃ N : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) N = 0 ∧
      ∀ a : A,
        dualAction (dualAction (mulLeft 𝕜 A)) a N -
          dualAction (dualAction (mulRight 𝕜 A)) a N =
        dualAction (dualAction (mulLeft 𝕜 A)) a E₀ -
          dualAction (dualAction (mulRight 𝕜 A)) a E₀ := by
  have hclosed : IsClosed ((mul' 𝕜 A).range : Set A) := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    exact isClosed_univ
  let D₀ : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)) :=
    (dualAction (dualAction (mulLeft 𝕜 A))).flip E₀ -
      (dualAction (dualAction (mulRight 𝕜 A))).flip E₀
  obtain ⟨N, hN_ker, hN_comm⟩ := h.exists_mem_ker_precomp_precomp_eq_dualAction_sub hclosed
    (mulLeft_mul_apply (𝕜 := 𝕜) (A := A))
    (mulRight_mul_apply (𝕜 := 𝕜) (A := A))
    (mulLeft_mulRight_apply_comm (𝕜 := 𝕜) (A := A))
    (mem_ker_of_intertwine (N := ContinuousLinearMap.mul 𝕜 A) (mul'_mulLeft_apply (𝕜 := 𝕜)))
    (mem_ker_of_intertwine (N := (ContinuousLinearMap.mul 𝕜 A).flip) (mul'_mulRight_apply (𝕜 := 𝕜)))
    D₀ (commutatorDerivation_mulLeft_mulRight_mul E₀) fun a ↦ by
      rw [LinearMap.mem_ker]
      ext f
      simpa only [D₀, coe_coe, precomp_apply, comp_apply, sub_apply, flip_apply,
        dualAction_apply, sub_eq_zero, zero_apply] using hE₀ a f
  exact ⟨N, LinearMap.mem_ker.mp hN_ker, fun a ↦ (hN_comm a).symm⟩

/-- **Amenability implies the existence of a virtual diagonal.** Every amenable Banach algebra over
`ℝ` or `ℂ` has a virtual diagonal `M ∈ (A ⊗̂π A)**`. -/
theorem IsAmenable.exists_isVirtualDiagonal (h : IsAmenable 𝕜 A) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M := by
  obtain ⟨C, l, hl, hC⟩ := h.exists_isApproximateUnit
  have := hl.neBot
  obtain ⟨E₀, hE₀L, hE₀R⟩ :=
    exists_bidual_mul_comp_mul'_eq_of_isApproximateUnit (𝕜 := 𝕜) hl hC
  have hE₀ (a : A) (f : StrongDual 𝕜 A) :
      E₀ ((f.comp (mul' 𝕜 A)).comp (mulLeft 𝕜 A a)) =
        E₀ ((f.comp (mul' 𝕜 A)).comp (mulRight 𝕜 A a)) := by
    rw [comp_assoc, mul'_comp_mulLeft, ← comp_assoc, hE₀L,
      comp_assoc, mul'_comp_mulRight, ← comp_assoc, hE₀R]
  obtain ⟨N, hN0, hNcomm⟩ :=
    h.exists_ker_mul'_eq_commutator (mul'_surjective hC hl.tendsto_mul_right) E₀ hE₀
  refine ⟨E₀ - N, ⟨fun a ↦ ?_, fun a ↦ ?_⟩⟩
  · simpa only [map_sub] using sub_eq_sub_iff_sub_eq_sub.2 (hNcomm a).symm
  · rw [map_sub, hN0, sub_zero]
    ext f
    simpa only [dualAction_apply_apply, dualAction_apply, precomp_apply, comp_apply, dual_def]
      using hE₀L a f

/-- **Amenability implies the existence of a bounded approximate diagonal.** Every amenable Banach
algebra over `ℝ` or `ℂ` has a bounded approximate diagonal. -/
theorem IsAmenable.exists_isApproximateDiagonal (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter (CompletedProjectiveTensor 𝕜 A A)),
      IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C :=
  let ⟨M, hM⟩ := h.exists_isVirtualDiagonal
  ⟨‖M‖, hM.exists_isApproximateDiagonal⟩

/-- **Johnson's virtual-diagonal characterization of amenability.** A Banach algebra over `ℝ` or
`ℂ` is amenable if and only if it has a virtual diagonal in `(A ⊗̂π A)**`. -/
theorem isAmenable_iff_exists_isVirtualDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        IsVirtualDiagonal 𝕜 M :=
  ⟨fun h ↦ h.exists_isVirtualDiagonal, fun ⟨_, hM⟩ ↦ hM.isAmenable⟩

/-- **Johnson's approximate-diagonal characterization of amenability.** A Banach algebra over `ℝ`
or `ℂ` is amenable if and only if it has a bounded approximate diagonal. -/
theorem isAmenable_iff_exists_isApproximateDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ (C : ℝ) (l : Filter (CompletedProjectiveTensor 𝕜 A A)),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C :=
  isAmenable_iff_exists_isVirtualDiagonal.trans
    exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal

/-- Universe-polymorphic innerness for amenable Banach algebras over `ℝ` or `ℂ`: every bounded
derivation into the dual `E*` of a normed `A`-bimodule `E` in *any* universe (without requiring
completeness of `E`) is inner. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction' (h : IsAmenable 𝕜 A) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  let ⟨_, hM⟩ := h.exists_isVirtualDiagonal
  hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

/-- For an amenable Banach algebra `A` over `ℝ` or `ℂ`, the first bounded Hochschild cohomology
`H¹(A, E*)` vanishes for every normed `A`-bimodule `E` in any universe. -/
theorem IsAmenable.subsingleton_hochschildBimoduleCohomology_one (h : IsAmenable 𝕜 A)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (L R : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    Subsingleton (hochschildBimoduleCohomology (dualAction R) (dualAction L)
      (dualAction_mul_apply_of_right hR) (dualAction_mul_apply_of_left hL)
      (dualAction_apply_dualAction_apply_comm hLR) 1) :=
  (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).2
    (h.exists_eq_dualAction_sub_dualAction' hL hR hLR)

end DiagonalCharacterization

end TauCeti
