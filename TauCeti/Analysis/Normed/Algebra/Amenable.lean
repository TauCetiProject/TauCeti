/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Complex
public import TauCeti.Analysis.Normed.Algebra.VirtualDiagonal
import Mathlib.Algebra.Module.Shrink
import Mathlib.Analysis.Normed.Module.Shrink
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Analysis.Normed.Module.Dual.Goldstine
import TauCeti.Analysis.Normed.Operator.Restrict
import TauCeti.Analysis.Normed.Ring.ApproximateUnit

/-!
# Amenable Banach algebras and Johnson's diagonal theorem

A normed algebra `A` over `𝕜` is *amenable*, in the sense of B. E. Johnson, if for every Banach
`A`-bimodule `E` every bounded derivation `D : A → E*` into the dual bimodule is inner. Here a
bimodule is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`, with `a · x = L a x` and
`x · a = R a x`, and the dual `E*` carries the dual actions of
`TauCeti.Analysis.Normed.Module.Dual.Bimodule`: the left action is `dualAction R` and the right
action is `dualAction L`. A bounded derivation is a bounded operator `D` with
`D (a * b) = a · D b + D a · b`, and it is inner when `D a = a · φ - φ · a` for some `φ ∈ E*`.
For `A : Type u` the test bimodules range over `Type u`. Equivalently, the first bounded
Hochschild cohomology `H¹(A, E*)` vanishes for every such `E`.

We prove **Johnson's characterization of amenability**: a real or complex Banach algebra `A` is
amenable if and only if it has a virtual diagonal (`TauCeti.IsVirtualDiagonal`), and if and only if
it has a bounded approximate diagonal (`TauCeti.IsApproximateDiagonal`). Along the way we show that
every amenable real or complex normed algebra has a bounded two-sided approximate identity, and
deduce that in an amenable real or complex Banach algebra every bounded derivation into the dual of
a normed bimodule in *any* universe (without completeness) is inner.

## Main definitions

* `TauCeti.IsAmenable`: amenability of a normed algebra.

## Main results

* `TauCeti.IsApproximateDiagonal.exists_eq_dualAction_sub_dualAction` and
  `TauCeti.IsVirtualDiagonal.exists_eq_dualAction_sub_dualAction`: if `A` has a bounded approximate
  diagonal (over a proper field) or a virtual diagonal (over a complete field), every bounded
  derivation of `A` into the dual of a normed bimodule in any universe is inner.
* `TauCeti.isAmenable_iff_forall_subsingleton_hochschildBimoduleCohomology_one`: amenability is
  the vanishing of `H¹(A, E*)` for all Banach bimodules `E`.
* `TauCeti.IsApproximateDiagonal.isAmenable` and `TauCeti.IsVirtualDiagonal.isAmenable`: a Banach
  algebra with a bounded approximate diagonal or a virtual diagonal is amenable.
* `TauCeti.IsAmenable.exists_isApproximateUnit`: an amenable real or complex normed algebra has a
  bounded two-sided approximate identity.
* `TauCeti.IsAmenable.exists_isVirtualDiagonal`, `TauCeti.IsAmenable.exists_isApproximateDiagonal`,
  `TauCeti.isAmenable_iff_exists_isVirtualDiagonal`, and
  `TauCeti.isAmenable_iff_exists_isApproximateDiagonal`: Johnson's equivalence between amenability,
  existence of a virtual diagonal, and existence of a bounded approximate diagonal.
* `TauCeti.IsAmenable.exists_eq_dualAction_sub_dualAction'` and
  `TauCeti.IsAmenable.subsingleton_hochschildBimoduleCohomology_one`: universe-polymorphic
  vanishing of bounded derivations and `H¹(A, E*)` for normed bimodules in any universe (without
  completeness).

## Implementation notes

For the sufficiency of a virtual diagonal `M ∈ (A ⊗̂π A)**`, no compactness or completeness of `E`
is needed: pulling `M` and `Δ** M ∈ A**` back along the operator `Φ : A ⊗̂π A → E*` induced by
`(a, b) ↦ a · D b` and along `D` produces functionals `φ`, `ψ`, and `ρ` in `E*` directly, and the
same algebraic calculation as in the ultrafilter argument shows that `D` is the inner derivation of
`φ + ρ - ψ`.

For the converse over `ℝ` or `ℂ`, amenability is first applied to the one-sided bimodule structures
on `A*` to obtain bounded left and right approximate identities via Goldstine's theorem, combined
into a bounded two-sided approximate identity `(e)` by Dixon's formula. A weak-star cluster point
`E₀ ∈ (A ⊗̂π A)**` of `e ⊗ e` satisfies `a · Δ** E₀ = J_A a` and `Δ** E₀ · a = J_A a` (using that
`(e²)` is also an approximate identity), so `a ↦ a · E₀ - E₀ · a` takes values in `ker Δ**`. By
Cohen's factorization theorem `Δ : A ⊗̂π A → A` is surjective, so the closed-range theorem
identifies `ker Δ**` isometrically with `(ker Δ)**` via
`ContinuousLinearMap.kerBidualEquivKerPrecompPrecomp`. Subtracting the bidual pushforward of the
resulting inner-derivation generator `N₀ ∈ (ker Δ)**` from `E₀` produces a virtual diagonal, and
Goldstine–Mazur (`TauCeti.IsVirtualDiagonal.exists_isApproximateDiagonal`) upgrades it to a bounded
approximate diagonal. Because `𝕜 : Type v` may live in a larger universe than `A : Type u`, the
dual test modules `A*` and `(ker Δ)*` are transferred to `Type u` via `Shrink`.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.1–2.2, Theorems 2.2.1 and 2.2.4.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§2.8–2.9.
-/

public section

noncomputable section

universe u v

open Filter NormedSpace Topology ContinuousLinearMap

open scoped TensorProduct

namespace TauCeti

open CompletedProjectiveTensor

section Derivation

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {L R : A →L[𝕜] E →L[𝕜] E}

attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

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

/-- If a Banach algebra `A` over a complete field has a virtual diagonal, then every bounded
derivation `D` of `A` into the dual `E*` of a normed `A`-bimodule `E` (in any universe, without
completeness of `E`) is inner. -/
theorem IsVirtualDiagonal.exists_eq_dualAction_sub_dualAction [CompleteSpace 𝕜]
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  let Φ := leftDerivationLift R D
  let E₁ : StrongDual 𝕜 (StrongDual 𝕜 A) :=
    precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A) :
      StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)) M
  let φ : StrongDual 𝕜 E := M.comp Φ.flip
  let ψ : StrongDual 𝕜 E := E₁.comp D.flip
  let ρ : StrongDual 𝕜 E := E₁.comp ((dualAction R).flip ψ).flip
  have hDφψ (a : A) (x : E) : D a x = φ (R a x) - φ (L a x) + ψ (L a x) := by
    have hg : Φ.flip (R a x) - Φ.flip (L a x) =
        (dualAction (mulLeft 𝕜 A) a (Φ.flip x) - dualAction (mulRight 𝕜 A) a (Φ.flip x)) +
          (precomp 𝕜 (mul' 𝕜 A) (dualAction (ContinuousLinearMap.mul 𝕜 A).flip a (D.flip x)) -
            precomp 𝕜 (mul' 𝕜 A) (D.flip (L a x))) := by
      refine DFunLike.ext _ _ fun m ↦ ?_
      have hcomm := congr($(dualAction_leftDerivationLift_sub hR hLR hD a m) x)
      simp only [Φ, map_sub, sub_apply, add_apply, comp_apply, precomp_apply,
        dualAction_apply_apply, flip_apply, mul_apply', hD (mul' 𝕜 A m) a] at hcomm ⊢
      linear_combination hcomm
    have h₁ := congr($(hM.dualAction_mulLeft_eq a) (Φ.flip x))
    have h₂ := congr($(hM.dualAction_mul_flip_precomp_mul' a) (D.flip x))
    simp only [dualAction_apply_apply, precomp_apply, comp_apply, dual_def] at h₁ h₂
    have hM_eq : φ (R a x) - φ (L a x) = M (Φ.flip (R a x) - Φ.flip (L a x)) := by
      simp [φ, ← map_sub]
    rw [hM_eq, hg, map_add, map_sub, map_sub, h₁, sub_self, zero_add, precomp_apply, precomp_apply,
      h₂]
    simp [ψ, E₁]
  have hψLR (a b : A) (x : E) : ψ (R a (L b x)) = 0 := by
    have := congr($(hD a b) x)
    simp only [dualAction_apply_apply, add_apply, hDφψ, hL, hR, hLR] at this
    linear_combination -this
  have hρR (a : A) (x : E) : ρ (R a x) = ψ (R a x) := by
    have hEq : ((dualAction R).flip ψ).flip (R a x) =
        dualAction (ContinuousLinearMap.mul 𝕜 A) a (((dualAction R).flip ψ).flip x) := by
      ext e
      simp [hR]
    have h₃ := congr($(hM.dualAction_mul_precomp_mul' a) (((dualAction R).flip ψ).flip x))
    simpa [ρ, E₁, hEq] using h₃
  have hρL (a : A) (x : E) : ρ (L a x) = 0 := by
    have hEq : ((dualAction R).flip ψ).flip (L a x) = 0 := by
      ext e
      simp [hψLR]
    simp [ρ, hEq]
  refine ⟨φ + ρ - ψ, fun a ↦ ?_⟩
  ext x
  simp only [dualAction_apply_apply, sub_apply, add_apply, hDφψ, hρR, hρL]
  ring

variable {l : Filter (CompletedProjectiveTensor 𝕜 A A)}

/-- If a Banach algebra `A` over a proper nontrivially normed field has a bounded approximate
diagonal, then every bounded derivation `D` of `A` into the dual `E*` of a normed `A`-bimodule `E`
is inner. Neither `A` nor the actions need to be unital, the actions need not be contractive, and
`E` need not be complete or essential. -/
theorem IsApproximateDiagonal.exists_eq_dualAction_sub_dualAction [ProperSpace 𝕜]
    (h : IsApproximateDiagonal 𝕜 l) {C : ℝ} (hC : ∀ᶠ m in l, ‖m‖ ≤ C)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  let ⟨_, _, hM⟩ := h.exists_isVirtualDiagonal hC
  hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

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

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- Transporting a `Small.{u}` Banach bimodule across `Shrink.{u}` makes every bounded derivation
into its dual inner whenever `A : Type u` is amenable. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction_of_small (h : IsAmenable 𝕜 A) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [Small.{u} E]
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  let e : Shrink.{u} E ≃ₗᵢ[𝕜] E :=
    { toLinearEquiv := Shrink.linearEquiv 𝕜 E
      norm_map' := fun _ ↦ rfl }
  have : CompleteSpace (Shrink.{u} E) := e.toIsometryEquiv.completeSpace
  let eCLM : Shrink.{u} E →L[𝕜] E := e.toLinearIsometry.toContinuousLinearMap
  let eSymmCLM : E →L[𝕜] Shrink.{u} E := e.symm.toLinearIsometry.toContinuousLinearMap
  let conj : (E →L[𝕜] E) →L[𝕜] Shrink.{u} E →L[𝕜] Shrink.{u} E :=
    (compL 𝕜 (Shrink.{u} E) E (Shrink.{u} E) eSymmCLM).comp
      ((compL 𝕜 (Shrink.{u} E) E E).flip eCLM)
  let L' := conj.comp L
  let R' := conj.comp R
  let D' : A →L[𝕜] StrongDual 𝕜 (Shrink.{u} E) :=
    (precomp 𝕜 eCLM : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 (Shrink.{u} E)).comp D
  have hL' (a b : A) (x : Shrink.{u} E) : L' (a * b) x = L' a (L' b x) := by
    simp [L', conj, eCLM, eSymmCLM, hL]
  have hR' (a b : A) (x : Shrink.{u} E) : R' (a * b) x = R' b (R' a x) := by
    simp [R', conj, eCLM, eSymmCLM, hR]
  have hLR' (a b : A) (x : Shrink.{u} E) : L' a (R' b x) = R' b (L' a x) := by
    simp [L', R', conj, eCLM, eSymmCLM, hLR]
  have hD' (a b : A) : D' (a * b) = dualAction R' a (D' b) + dualAction L' b (D' a) := by
    ext x
    simpa [D', L', R', conj, eCLM, eSymmCLM] using congr($(hD a b) (e x))
  obtain ⟨φ', hφ'⟩ := h.exists_eq_dualAction_sub_dualAction hL' hR' hLR' D' hD'
  refine ⟨φ'.comp eSymmCLM, fun a ↦ ?_⟩
  ext y
  simpa [D', L', R', conj, eCLM, eSymmCLM] using congr($(hφ' a) (e.symm y))

/-- A Banach algebra over a complete field with a virtual diagonal is amenable. -/
theorem IsVirtualDiagonal.isAmenable [CompleteSpace 𝕜] [CompleteSpace A]
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (h : IsVirtualDiagonal 𝕜 M) : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ hL hR hLR D hD ↦ h.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

/-- A Banach algebra with a bounded approximate diagonal is amenable. -/
theorem IsApproximateDiagonal.isAmenable [ProperSpace 𝕜] [CompleteSpace A]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (h : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ hL hR hLR D hD ↦ h.exists_eq_dualAction_sub_dualAction hC hL hR hLR D hD

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- A subsingleton normed algebra is amenable. -/
theorem isAmenable_of_subsingleton [Subsingleton A] : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ _ _ _ _ _ ↦ ⟨0, fun a ↦ by simp [Subsingleton.elim a 0]⟩

variable (𝕜) in
/-- The base field, with the diagonal `1 ⊗ 1`, is amenable over itself. -/
theorem isAmenable_self [CompleteSpace 𝕜] : IsAmenable 𝕜 𝕜 :=
  (isVirtualDiagonal_inclusionInDoubleDual_one_tmul_one 𝕜).isAmenable

end Amenable

section Johnson

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

/-- Every `RCLike` field is `Small` in any universe, since `re` and `im` embed it into `ℝ × ℝ`. -/
private theorem small_rclike : Small.{u} 𝕜 :=
  small_of_injective (β := ℝ × ℝ) (f := fun z ↦ (RCLike.re z, RCLike.im z)) fun _ _ h ↦
    RCLike.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- An amenable normed algebra over `ℝ` or `ℂ` has a bounded right approximate identity, obtained
by applying amenability to `A*` with trivial left action and right action dual to left
multiplication. -/
private theorem exists_tendsto_mul_left_of_isAmenable (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ f in l, ‖f‖ ≤ C) ∧ ∀ a, Tendsto (a * ·) l (𝓝 a) := by
  have : Small.{u} 𝕜 := small_rclike
  have : Small.{u} (StrongDual 𝕜 A) := small_of_injective DFunLike.coe_injective
  let R : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A :=
    dualAction (ContinuousLinearMap.mul 𝕜 A)
  have hR (a b : A) (f : StrongDual 𝕜 A) : R (a * b) f = R b (R a f) :=
    dualAction_mul_apply_of_left (fun x y z ↦ by simp [mul_assoc]) a b f
  have hD (a b : A) :
      inclusionInDoubleDual 𝕜 A (a * b) =
        dualAction R a (inclusionInDoubleDual 𝕜 A b) +
          dualAction (0 : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A) b
            (inclusionInDoubleDual 𝕜 A a) := by
    ext f
    simp [R, dual_def]
  obtain ⟨E, hE⟩ := h.exists_eq_dualAction_sub_dualAction_of_small
    (L := 0) (R := R) (fun _ _ _ ↦ by simp) hR (fun _ _ _ ↦ by simp) (inclusionInDoubleDual 𝕜 A) hD
  have hT (a : A) :
      precomp 𝕜 (precomp 𝕜 (ContinuousLinearMap.mul 𝕜 A a) :
          StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A) E =
        inclusionInDoubleDual 𝕜 A a := by
    ext f
    simpa [R, dualAction_apply] using (congr($(hE a) f)).symm
  obtain ⟨l, hl, hbound, htend⟩ :=
    E.exists_neBot_tendsto_of_forall_precomp_precomp_eq le_rfl
      (fun a ↦ ContinuousLinearMap.mul 𝕜 A a) id hT
  exact ⟨‖E‖, l, hl, hbound, htend⟩

/-- An amenable normed algebra over `ℝ` or `ℂ` has a bounded left approximate identity, obtained
by applying amenability to `A*` with left action dual to right multiplication and trivial right
action. -/
private theorem exists_tendsto_mul_right_of_isAmenable (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (· * a) l (𝓝 a) := by
  have : Small.{u} 𝕜 := small_rclike
  have : Small.{u} (StrongDual 𝕜 A) := small_of_injective DFunLike.coe_injective
  let L : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A :=
    dualAction (ContinuousLinearMap.mul 𝕜 A).flip
  have hL (a b : A) (f : StrongDual 𝕜 A) : L (a * b) f = L a (L b f) :=
    dualAction_mul_apply_of_right (fun x y z ↦ by simp [mul_assoc]) a b f
  have hD (a b : A) :
      inclusionInDoubleDual 𝕜 A (a * b) =
        dualAction (0 : A →L[𝕜] StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A) a
          (inclusionInDoubleDual 𝕜 A b) +
          dualAction L b (inclusionInDoubleDual 𝕜 A a) := by
    ext f
    simp [L, dual_def]
  obtain ⟨E, hE⟩ := h.exists_eq_dualAction_sub_dualAction_of_small
    (L := L) (R := 0) hL (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (inclusionInDoubleDual 𝕜 A) hD
  have hT (a : A) :
      precomp 𝕜 (precomp 𝕜 ((ContinuousLinearMap.mul 𝕜 A).flip a) :
          StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 A) (-E) =
        inclusionInDoubleDual 𝕜 A a := by
    ext f
    simpa [L, dualAction_apply] using (congr($(hE a) f)).symm
  obtain ⟨l, hl, hbound, htend⟩ :=
    (-E).exists_neBot_tendsto_of_forall_precomp_precomp_eq le_rfl
      (fun a ↦ (ContinuousLinearMap.mul 𝕜 A).flip a) id hT
  exact ⟨‖-E‖, l, hl, hbound, htend⟩

/-- An amenable normed algebra over `ℝ` or `ℂ` has a bounded two-sided approximate identity. -/
theorem IsAmenable.exists_isApproximateUnit (h : IsAmenable 𝕜 A) :
    ∃ l : Filter A, l.IsApproximateUnit ∧ ∃ C, ∀ᶠ e in l, ‖e‖ ≤ C := by
  obtain ⟨C₁, l₁, hl₁, hC₁, ht₁⟩ := exists_tendsto_mul_right_of_isAmenable h
  obtain ⟨C₂, l₂, hl₂, hC₂, ht₂⟩ := exists_tendsto_mul_left_of_isAmenable h
  obtain ⟨l, hl, hbound⟩ :=
    exists_isApproximateUnit_of_left_of_right ⟨l₁, hl₁, hC₁, ht₁⟩ ⟨l₂, hl₂, hC₂, ht₂⟩
  exact ⟨l, hl, _, hbound⟩

section

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The bidual adjoint `T** : X** →L[𝕜] A**` of a bounded operator `T : X →L[𝕜] A`. -/
private def bidualMap {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] A) :
    StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 A) :=
  precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 X)

private theorem bidualMap_apply {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] A) (M : StrongDual 𝕜 (StrongDual 𝕜 X)) :
    bidualMap T M = precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 A →L[𝕜] StrongDual 𝕜 X) M := rfl

/-- The bidual inclusion `(ker T)** →L[𝕜] X**` for `T : X →L[𝕜] A`. -/
private def bidualKerMap {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] A) :
    StrongDual 𝕜 (StrongDual 𝕜 T.ker) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X) :=
  precomp 𝕜 (precomp 𝕜 T.ker.subtypeL : StrongDual 𝕜 X →L[𝕜] StrongDual 𝕜 T.ker)

private theorem bidualKerMap_apply {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] A) (Φ : StrongDual 𝕜 (StrongDual 𝕜 T.ker)) :
    bidualKerMap T Φ =
      precomp 𝕜 (precomp 𝕜 T.ker.subtypeL : StrongDual 𝕜 X →L[𝕜] StrongDual 𝕜 T.ker) Φ := rfl

private theorem mem_ker_of_map_left {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    {L : A →L[𝕜] X →L[𝕜] X} {T : X →L[𝕜] A} (hTL : ∀ a x, T (L a x) = a * T x)
    (a : A) {x : X} (hx : x ∈ T.ker) : L a x ∈ T.ker := by
  simp only [LinearMap.mem_ker, coe_coe] at hx ⊢
  rw [hTL, hx, mul_zero]

private theorem mem_ker_of_map_right {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    {R : A →L[𝕜] X →L[𝕜] X} {T : X →L[𝕜] A} (hTR : ∀ a x, T (R a x) = T x * a)
    (a : A) {x : X} (hx : x ∈ T.ker) : R a x ∈ T.ker := by
  simp only [LinearMap.mem_ker, coe_coe] at hx ⊢
  rw [hTR, hx, zero_mul]

/-- Restriction of a bounded action `M` on `X` to an invariant kernel `T.ker`. -/
private def kerAction {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : A →L[𝕜] X →L[𝕜] X) (T : X →L[𝕜] A)
    (hM : ∀ a {x : X}, x ∈ T.ker → M a x ∈ T.ker) :
    A →L[𝕜] T.ker →L[𝕜] T.ker :=
  M.restrictAction T.ker fun a _ hx ↦ hM a hx

@[simp]
private theorem coe_kerAction_apply {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : A →L[𝕜] X →L[𝕜] X) (T : X →L[𝕜] A)
    (hM : ∀ a {x : X}, x ∈ T.ker → M a x ∈ T.ker) (a : A) (x : T.ker) :
    (kerAction M T hM a x : X) = M a x :=
  coe_restrictAction_apply _ _ _ a x

private theorem dualAction_kerAction_comp_subtypeL {X : Type*} [SeminormedAddCommGroup X]
    [NormedSpace 𝕜 X] (M : A →L[𝕜] X →L[𝕜] X) (T : X →L[𝕜] A)
    (hM : ∀ a {x : X}, x ∈ T.ker → M a x ∈ T.ker) (a : A) (f : StrongDual 𝕜 X) :
    dualAction (kerAction M T hM) a (f.comp T.ker.subtypeL) =
      (dualAction M a f).comp T.ker.subtypeL := by
  ext x
  simp

end

variable [CompleteSpace A]

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- Pulling `a ↦ a · E₀ - E₀ · a ∈ ker T**` across `kerBidualEquivKerPrecompPrecomp` gives a
bounded derivation `A →L[𝕜] (ker T)**`. -/
private theorem exists_derivation_ker {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] {L R : A →L[𝕜] X →L[𝕜] X} {T : X →L[𝕜] A}
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (hTL : ∀ a x, T (L a x) = a * T x)
    (hTR : ∀ a x, T (R a x) = T x * a)
    (hclosed : IsClosed (T.range : Set A))
    (E₀ : StrongDual 𝕜 (StrongDual 𝕜 X))
    (hker : ∀ a : A,
      dualAction (dualAction L) a E₀ - dualAction (dualAction R) a E₀ ∈ (bidualMap T).ker) :
    ∃ D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 T.ker),
      (∀ a (f : StrongDual 𝕜 X),
        D a (f.comp T.ker.subtypeL) =
          E₀ (dualAction L a f) - E₀ (dualAction R a f)) ∧
      ∀ a b, D (a * b) =
        dualAction (dualAction (kerAction L T (mem_ker_of_map_left hTL))) a (D b) +
          dualAction (dualAction (kerAction R T (mem_ker_of_map_right hTR))) b (D a) := by
  let bL := dualAction (dualAction L)
  let bR := dualAction (dualAction R)
  let D₀ := bL.flip E₀ - bR.flip E₀
  let e := T.kerBidualEquivKerPrecompPrecomp hclosed
  let D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 T.ker) :=
    e.symm.toLinearIsometry.toContinuousLinearMap.comp (D₀.codRestrict (bidualMap T).ker hker)
  have hD_iota (a : A) : bidualKerMap T (D a) = bL a E₀ - bR a E₀ := by
    rw [bidualKerMap_apply, ← T.coe_kerBidualEquivKerPrecompPrecomp_apply hclosed]
    exact congrArg Subtype.val (e.apply_symm_apply (D₀.codRestrict (bidualMap T).ker hker a))
  have hD_eval (a : A) (f : StrongDual 𝕜 X) :
      D a (f.comp T.ker.subtypeL) = E₀ (dualAction L a f) - E₀ (dualAction R a f) := by
    simpa only [bL, bR, bidualKerMap_apply, precomp_apply, comp_apply, sub_apply,
      dualAction_apply_apply] using congr($(hD_iota a) f)
  refine ⟨D, hD_eval, fun a b ↦ ?_⟩
  ext g
  obtain ⟨f, rfl⟩ := T.ker.surjective_precomp_subtypeL g
  rw [precomp_apply, add_apply, dualAction_apply_apply, dualAction_apply_apply,
    dualAction_kerAction_comp_subtypeL, dualAction_kerAction_comp_subtypeL,
    hD_eval, hD_eval, hD_eval,
    dualAction_mul_apply_of_left hL a b f, dualAction_mul_apply_of_right hR a b f,
    dualAction_apply_dualAction_apply_comm hLR b a f]
  abel

/-- Correcting `E₀ ∈ X**` along `ker T**` using amenability on `(ker T)**` produces `M ∈ X**` with
`a · M = M · a` and `T** M = T** E₀`. -/
private theorem exists_bidual_intertwining_of_isAmenable (h : IsAmenable 𝕜 A)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [Small.{u} (StrongDual 𝕜 X)] {L R : A →L[𝕜] X →L[𝕜] X} {T : X →L[𝕜] A}
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (hTL : ∀ a x, T (L a x) = a * T x)
    (hTR : ∀ a x, T (R a x) = T x * a)
    (hclosed : IsClosed (T.range : Set A))
    (E₀ : StrongDual 𝕜 (StrongDual 𝕜 X))
    (hE₀_left : ∀ a : A,
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a (bidualMap T E₀) =
        inclusionInDoubleDual 𝕜 A a)
    (hE₀_ker : ∀ a : A,
      dualAction (dualAction L) a E₀ - dualAction (dualAction R) a E₀ ∈ (bidualMap T).ker) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 X),
      (∀ a : A, dualAction (dualAction L) a M = dualAction (dualAction R) a M) ∧
      ∀ a : A, dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a
        (precomp 𝕜 (precomp 𝕜 T) M) = inclusionInDoubleDual 𝕜 A a := by
  obtain ⟨D, hD_eval, hD⟩ := exists_derivation_ker hL hR hLR hTL hTR hclosed E₀ hE₀_ker
  have : Small.{u} (StrongDual 𝕜 T.ker) := small_of_surjective T.ker.surjective_precomp_subtypeL
  let kL := kerAction L T (mem_ker_of_map_left hTL)
  let kR := kerAction R T (mem_ker_of_map_right hTR)
  have hkL (a b : A) (x : T.ker) : kL (a * b) x = kL a (kL b x) := Subtype.ext (by simp [kL, hL])
  have hkR (a b : A) (x : T.ker) : kR (a * b) x = kR b (kR a x) := Subtype.ext (by simp [kR, hR])
  have hkLR (a b : A) (x : T.ker) : kL a (kR b x) = kR b (kL a x) :=
    Subtype.ext (by simp [kL, kR, hLR])
  obtain ⟨N₀, hN₀⟩ := h.exists_eq_dualAction_sub_dualAction_of_small
    (L := dualAction kR) (R := dualAction kL)
    (dualAction_mul_apply_of_right hkR) (dualAction_mul_apply_of_left hkL)
    (dualAction_apply_dualAction_apply_comm hkLR) D hD
  refine ⟨E₀ - bidualKerMap T N₀, ?_, ?_⟩
  · intro a
    ext f
    have hN₀_eval := congr($(hN₀ a) (f.comp T.ker.subtypeL))
    rw [hD_eval, sub_apply, dualAction_apply_apply, dualAction_apply_apply,
      dualAction_kerAction_comp_subtypeL, dualAction_kerAction_comp_subtypeL] at hN₀_eval
    simp only [dualAction_apply_apply, sub_apply, bidualKerMap_apply, precomp_apply, comp_apply]
    linear_combination hN₀_eval
  · intro a
    have hker_N₀ : bidualMap T (bidualKerMap T N₀) = 0 := by
      have hm := (T.kerBidualEquivKerPrecompPrecomp hclosed N₀).2
      rw [bidualMap_apply, bidualKerMap_apply]
      rwa [LinearMap.mem_ker, coe_coe, T.coe_kerBidualEquivKerPrecompPrecomp_apply] at hm
    rw [← bidualMap_apply T (E₀ - bidualKerMap T N₀), map_sub, hker_N₀, sub_zero]
    exact hE₀_left a

/-- A weak-star cluster point `E₀ ∈ (A ⊗̂π A)**` of `e ↦ e ⊗ e` along a bounded two-sided
approximate identity satisfies `a · Δ** E₀ = J_A a` and `a · E₀ - E₀ · a ∈ ker Δ**`. -/
private theorem exists_bidual_of_isApproximateUnit {l : Filter A} (hl : l.IsApproximateUnit)
    {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    ∃ E₀ : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      (∀ a : A,
        dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a (bidualMap (mul' 𝕜 A) E₀) =
          inclusionInDoubleDual 𝕜 A a) ∧
      ∀ a : A,
        dualAction (dualAction (mulLeft 𝕜 A)) a E₀ -
          dualAction (dualAction (mulRight 𝕜 A)) a E₀ ∈ (bidualMap (mul' 𝕜 A)).ker := by
  have := hl.neBot
  obtain ⟨e₀, he₀⟩ := hC.exists
  have hC0 : 0 ≤ C := (norm_nonneg e₀).trans he₀
  let u : A → CompletedProjectiveTensor 𝕜 A A := fun e ↦ (⟨e ⊗ₜ e⟩ : ProjectiveTensor 𝕜 A A)
  have hu : ∀ᶠ m in l.map u, ‖m‖ ≤ C * C :=
    eventually_map.2 <| hC.mono fun e he ↦
      (norm_coe_tmul_le e e).trans (mul_le_mul he he (norm_nonneg e) hC0)
  obtain ⟨E₀, -, hE₀⟩ := hu.exists_mapClusterPt_inclusionInDoubleDual (𝕜 := 𝕜)
  have hsq := hl.map_mul_self hC
  have hleft (a : A) :
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a (bidualMap (mul' 𝕜 A) E₀) =
        inclusionInDoubleDual 𝕜 A a := by
    ext f
    rw [dualAction_apply_apply, bidualMap_apply, precomp_apply, comp_apply, precomp_apply,
      dual_def]
    refine hE₀.apply_eq_of_tendsto_inclusionInDoubleDual _ (tendsto_map'_iff.2 ?_)
    simpa only [u, Function.comp_def, comp_apply, dualAction_apply_apply, mul_apply',
      mul'_coe_tmul] using
      (f.continuous.tendsto a).comp (tendsto_map'_iff.1 (hsq.tendsto_mul_left a))
  have hright (a : A) :
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) a (bidualMap (mul' 𝕜 A) E₀) =
        inclusionInDoubleDual 𝕜 A a := by
    ext f
    rw [dualAction_apply_apply, bidualMap_apply, precomp_apply, comp_apply, precomp_apply,
      dual_def]
    refine hE₀.apply_eq_of_tendsto_inclusionInDoubleDual _ (tendsto_map'_iff.2 ?_)
    simpa only [u, Function.comp_def, comp_apply, dualAction_apply_apply, flip_apply, mul_apply',
      mul'_coe_tmul] using
      (f.continuous.tendsto a).comp (tendsto_map'_iff.1 (hsq.tendsto_mul_right a))
  refine ⟨E₀, hleft, fun a ↦ ?_⟩
  have hL := precomp_precomp_dualAction_dualAction_apply
    (M := mulLeft 𝕜 A) (N := ContinuousLinearMap.mul 𝕜 A) (T := mul' 𝕜 A)
    (fun c m ↦ mul'_mulLeft_apply c m) a E₀
  have hR := precomp_precomp_dualAction_dualAction_apply
    (M := mulRight 𝕜 A) (N := (ContinuousLinearMap.mul 𝕜 A).flip) (T := mul' 𝕜 A)
    (fun c m ↦ mul'_mulRight_apply c m) a E₀
  rw [LinearMap.mem_ker, coe_coe, map_sub, sub_eq_zero, bidualMap_apply, bidualMap_apply, hL,
    hR, ← bidualMap_apply]
  exact (hleft a).trans (hright a).symm

/-- **Johnson's theorem (amenability implies virtual diagonal).** Every amenable Banach algebra
over `ℝ` or `ℂ` has a virtual diagonal. -/
theorem IsAmenable.exists_isVirtualDiagonal (h : IsAmenable 𝕜 A) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M := by
  obtain ⟨l, hl, C, hC⟩ := h.exists_isApproximateUnit
  have := hl.neBot
  obtain ⟨E₀, hE₀_left, hE₀_ker⟩ := exists_bidual_of_isApproximateUnit (𝕜 := 𝕜) hl hC
  have hsurj : Function.Surjective (mul' 𝕜 A) := mul'_surjective (𝕜 := 𝕜) hC hl.tendsto_mul_right
  have hclosed : IsClosed ((mul' 𝕜 A).range : Set A) := by
    rw [LinearMap.coe_range, coe_coe, hsurj.range_eq]
    exact isClosed_univ
  have : Small.{u} 𝕜 := small_rclike
  have : Small.{u} (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)) :=
    small_of_injective (f := fun f (p : A × A) ↦ f (⟨p.1 ⊗ₜ p.2⟩ : ProjectiveTensor 𝕜 A A))
      fun _ _ hf ↦ continuousLinearMap_ext fun x y ↦ congrFun hf (x, y)
  obtain ⟨M, hM₁, hM₂⟩ := exists_bidual_intertwining_of_isAmenable h
    mulLeft_mul_apply mulRight_mul_apply mulLeft_mulRight_apply_comm
    (fun a x ↦ mul'_mulLeft_apply a x) (fun a x ↦ mul'_mulRight_apply a x)
    hclosed E₀ hE₀_left hE₀_ker
  exact ⟨M, hM₁, hM₂⟩

/-- **Johnson's theorem (amenability implies bounded approximate diagonal).** Every amenable Banach
algebra over `ℝ` or `ℂ` has a bounded approximate diagonal. -/
theorem IsAmenable.exists_isApproximateDiagonal (h : IsAmenable 𝕜 A) :
    ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
      IsApproximateDiagonal 𝕜 l ∧ ∃ C, ∀ᶠ m in l, ‖m‖ ≤ C :=
  let ⟨M, hM⟩ := h.exists_isVirtualDiagonal
  let ⟨l, hl, hbound⟩ := hM.exists_isApproximateDiagonal
  ⟨l, hl, ‖M‖, hbound⟩

/-- **Johnson's theorem.** A Banach algebra over `ℝ` or `ℂ` is amenable if and only if it has a
virtual diagonal. -/
theorem isAmenable_iff_exists_isVirtualDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        IsVirtualDiagonal 𝕜 M :=
  ⟨IsAmenable.exists_isVirtualDiagonal, fun ⟨_, hM⟩ ↦ hM.isAmenable⟩

/-- **Johnson's theorem.** A Banach algebra over `ℝ` or `ℂ` is amenable if and only if it has a
bounded approximate diagonal. -/
theorem isAmenable_iff_exists_isApproximateDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ l : Filter (CompletedProjectiveTensor 𝕜 A A),
        IsApproximateDiagonal 𝕜 l ∧ ∃ C, ∀ᶠ m in l, ‖m‖ ≤ C :=
  ⟨IsAmenable.exists_isApproximateDiagonal, fun ⟨_, hl, _, hC⟩ ↦ hl.isAmenable hC⟩

/-- In an amenable Banach algebra over `ℝ` or `ℂ`, every bounded derivation into the dual `E*` of a
normed `A`-bimodule `E` in *any* universe (without completeness) is inner. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction' (h : IsAmenable 𝕜 A) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  let ⟨_, hM⟩ := h.exists_isVirtualDiagonal
  hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

end Johnson

section Cohomology

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- In an amenable Banach algebra over `ℝ` or `ℂ`, the first bounded Hochschild cohomology
`H¹(A, E*)` vanishes for every normed `A`-bimodule `E` in any universe (without completeness). -/
theorem IsAmenable.subsingleton_hochschildBimoduleCohomology_one (h : IsAmenable 𝕜 A)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (L R : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    Subsingleton (hochschildBimoduleCohomology (dualAction R) (dualAction L)
      (dualAction_mul_apply_of_right hR) (dualAction_mul_apply_of_left hL)
      (dualAction_apply_dualAction_apply_comm hLR) 1) :=
  (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).2
    (h.exists_eq_dualAction_sub_dualAction' hL hR hLR)

end Cohomology

end TauCeti
