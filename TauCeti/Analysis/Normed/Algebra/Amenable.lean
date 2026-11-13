/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.ApproximateDiagonal
public import TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Complex
public import TauCeti.Analysis.Normed.Module.Dual.Bimodule

/-!
# Amenable Banach algebras

A normed algebra `A` over `𝕜` is *amenable*, in the sense of B. E. Johnson, if for every Banach
`A`-bimodule `E` every bounded derivation `D : A → E*` into the dual bimodule is inner. Here a
bimodule is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`, with `a · x = L a x` and
`x · a = R a x`, and the dual `E*` carries the dual actions of
`TauCeti.Analysis.Normed.Module.Dual.Bimodule`: the left action is `dualAction R` and the right
action is `dualAction L`. A bounded derivation is a bounded operator `D` with
`D (a * b) = a · D b + D a · b`, and it is inner when `D a = a · φ - φ · a` for some `φ ∈ E*`.
For `A : Type u` the test bimodules range over `Type u`. Equivalently, the first bounded
Hochschild cohomology `H¹(A, E*)` vanishes for every such `E`.

The main result is Johnson's sufficient condition: a Banach algebra with a bounded approximate
diagonal is amenable, and in fact every bounded derivation into the dual of a bimodule in any
universe is inner. This is one implication of Johnson's characterization of amenability by
bounded approximate diagonals.

## Main definitions

* `TauCeti.IsAmenable`: amenability of a normed algebra.

## Main results

* `TauCeti.IsApproximateDiagonal.exists_eq_dualAction_sub_dualAction`: if `A` has a bounded
  approximate diagonal, every bounded derivation of `A` into the dual of a bounded bimodule is
  inner.
* `TauCeti.isAmenable_def` and `TauCeti.IsAmenable.exists_eq_dualAction_sub_dualAction`: the
  characteristic property of amenability, and its use on a given bounded derivation.
* `TauCeti.isAmenable_iff_forall_subsingleton_hochschildBimoduleCohomology_one`: amenability is
  the vanishing of `H¹(A, E*)` for all Banach bimodules `E`.
* `TauCeti.IsApproximateDiagonal.isAmenable`: a Banach algebra with a bounded approximate
  diagonal is amenable.
* `TauCeti.isAmenable_self`: the base field is amenable over itself.

## Implementation notes

The proof is the classical one, except that it needs no reduction to essential bimodules. Fix an
ultrafilter finer than the approximate diagonal, write `e = Δ m` for the image
of `m` under the multiplication map, and let `Φ : A ⊗̂π A → E*` be the bounded operator induced
by the bilinear map `(a, b) ↦ a · D b`. The derivation rule gives

`a · Φ m - Φ m · a = Φ (a · m - m · a) + e · D a` and `e · D a = D (e * a) - D e · a`.

By Banach–Alaoglu, the bounded families `Φ m`, `D e` and `e · ψ` have weak-star limits `φ`, `ψ`
and `ρ` along the ultrafilter. The two identities give `D a = a · φ - φ · a + ψ · a`. Since `D`
and the inner derivation of `φ` are derivations, `a · (ψ · b) = 0`, whence `a · ρ = a · ψ` and
`ρ · a = 0`. Thus `D` is the inner derivation of `φ + ρ - ψ`.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.1 and Theorem 2.2.4.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
-/

public section

noncomputable section

universe u v

open Filter Topology ContinuousLinearMap

namespace TauCeti

open CompletedProjectiveTensor

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

variable {l : Filter (CompletedProjectiveTensor 𝕜 A A)}

/-- Let `φ` and `ψ` be pointwise limits of `Φ m` and `D (Δ m)` along a proper filter finer than
an approximate diagonal, where `Φ` is induced by `(a, b) ↦ a · D b`. Then
`D a = a · φ - φ · a + ψ · a`. -/
private theorem apply_eq_of_tendsto [CompleteSpace 𝕜] (h : IsApproximateDiagonal 𝕜 l)
    {U : Filter (CompletedProjectiveTensor 𝕜 A A)} [U.NeBot] (hU : U ≤ l)
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) {φ ψ : StrongDual 𝕜 E}
    (hφ : ∀ x, Tendsto (leftDerivationLift R D · x) U (𝓝 (φ x)))
    (hψ : ∀ x, Tendsto (fun m ↦ D (mul' 𝕜 A m) x) U (𝓝 (ψ x))) (a : A) (x : E) :
    D a x = φ (R a x) - φ (L a x) + ψ (L a x) := by
  set Φ := leftDerivationLift R D
  -- `a · Φ m - Φ m · a` tends to `a · φ - φ · a`.
  have h₁ : Tendsto (fun m ↦ (dualAction R a (Φ m) - dualAction L a (Φ m)) x) U
      (𝓝 (φ (R a x) - φ (L a x))) := by
    simpa using (hφ (R a x)).sub (hφ (L a x))
  -- `Φ (a · m - m · a) → 0`, `D (Δ m * a) → D a` and `D (Δ m) · a → ψ · a`.
  have hcomm : Tendsto (fun m ↦ Φ (mulLeft 𝕜 A a m - mulRight 𝕜 A a m) x) U (𝓝 0) :=
    (((Φ.continuous.clm_apply (continuous_const (y := x))).tendsto' 0 0 (by simp)).comp
      (h.tendsto_mulLeft_sub_mulRight a)).mono_left hU
  have hDe : Tendsto (fun m ↦ D (mul' 𝕜 A m * a) x) U (𝓝 (D a x)) :=
    ((D.continuous.clm_apply (continuous_const (y := x))).tendsto a).comp <|
      (tendsto_map'_iff.1 (h.isApproximateUnit_map.tendsto_mul_right a)).mono_left hU
  have h₂ : Tendsto (fun m ↦ (dualAction R a (Φ m) - dualAction L a (Φ m)) x) U
      (𝓝 (0 + (D a x - ψ (L a x)))) := by
    refine (hcomm.add (hDe.sub (hψ (L a x)))).congr fun m ↦ ?_
    rw [dualAction_leftDerivationLift_sub hR hLR hD, hD]
    simp [Φ]
  rw [tendsto_nhds_unique h₁ h₂]
  ring

variable [ProperSpace 𝕜]

/-- If a Banach algebra `A` has a bounded approximate diagonal, then every bounded derivation `D`
of `A` into the dual `E*` of a bounded `A`-bimodule `E` is inner. The left and right actions of
`A` on `E*` are `dualAction R` and `dualAction L`, so the conclusion says `D a = a · φ - φ · a`
for some `φ ∈ E*`. Neither `A` nor the actions need to be unital, the actions need not be
contractive, and `E` need not be essential. -/
theorem IsApproximateDiagonal.exists_eq_dualAction_sub_dualAction
    (h : IsApproximateDiagonal 𝕜 l) {C : ℝ} (hC : ∀ᶠ m in l, ‖m‖ ≤ C)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have := h.neBot
  set U := Ultrafilter.of l
  have hU : (U : Filter _) ≤ l := Ultrafilter.of_le l
  -- Banach–Alaoglu: an eventually bounded family of functionals has a weak-star limit along `U`.
  have lim : ∀ (g : CompletedProjectiveTensor 𝕜 A A → StrongDual 𝕜 E) (r : ℝ),
      (∀ᶠ m in l, ‖g m‖ ≤ r) → ∃ φ : StrongDual 𝕜 E, ∀ x, Tendsto (g · x) U (𝓝 (φ x)) := by
    intro g r hg
    obtain ⟨φ, -, hφ⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) r).ultrafilter_le_nhds'
      (U.map (StrongDual.toWeakDual ∘ g))
      (Ultrafilter.mem_map.2 <| mem_of_superset (hU hg) fun m hm ↦ by simpa using hm)
    exact ⟨WeakDual.toStrongDual φ, fun x ↦ ((WeakDual.eval_continuous x).tendsto φ).comp hφ⟩
  have hCe : ∀ᶠ m in l, ‖mul' 𝕜 A m‖ ≤ C := hC.mono fun m hm ↦ (norm_mul'_apply_le m).trans hm
  have hC0 : ∀ᶠ _ in l, 0 ≤ C := hC.mono fun m hm ↦ (norm_nonneg m).trans hm
  obtain ⟨φ, hφ⟩ := lim (leftDerivationLift R D) (‖leftDerivationLift R D‖ * C) <|
    (hC.and hC0).mono fun m hm ↦ ((leftDerivationLift R D).le_opNorm m).trans
      (mul_le_mul_of_nonneg_left hm.1 (norm_nonneg _))
  obtain ⟨ψ, hψ⟩ := lim (fun m ↦ D (mul' 𝕜 A m)) (‖D‖ * C) <| hCe.mono fun m hm ↦
    (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left hm (norm_nonneg D))
  obtain ⟨ρ, hρ⟩ := lim (fun m ↦ dualAction R (mul' 𝕜 A m) ψ) (‖R‖ * C * ‖ψ‖) <|
    (hCe.and hC0).mono fun m hm ↦ by
      rw [dualAction_apply]
      refine (le_opNorm _ ψ).trans ?_
      gcongr
      exact (norm_precomp_le _).trans ((R.le_opNorm _).trans (by gcongr; exact hm.1))
  -- First, `D a = a · φ - φ · a + ψ · a`.
  have hDφψ := apply_eq_of_tendsto h hU hR hLR hD hφ hψ
  -- Since `D` is a derivation, `a · (ψ · b) = 0`, that is `ψ (b · x · a) = 0`.
  have hψLR (a b : A) (x : E) : ψ (R a (L b x)) = 0 := by
    have := congr($(hD a b) x)
    simp only [dualAction_apply_apply, add_apply, hDφψ, hL, hR, hLR] at this
    linear_combination -this
  -- Hence `a · ρ = a · ψ` and `ρ · a = 0`.
  have hρR (a : A) (x : E) : ρ (R a x) = ψ (R a x) := by
    refine tendsto_nhds_unique (hρ (R a x)) ?_
    have := ((ψ.continuous.comp (R.continuous.clm_apply (continuous_const (y := x)))).tendsto
      a).comp ((h.tendsto_mul_mul' a).mono_left hU)
    simpa [Function.comp_def, hR] using this
  have hρL (a : A) (x : E) : ρ (L a x) = 0 := by
    refine tendsto_nhds_unique (hρ (L a x)) ?_
    simp [hψLR]
  -- Therefore `D` is the inner derivation of `φ + ρ - ψ`.
  refine ⟨φ + ρ - ψ, fun a ↦ ?_⟩
  ext x
  simp only [dualAction_apply_apply, sub_apply, add_apply, hDφψ, hρR, hρL]
  ring

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

/-- A Banach algebra with a bounded approximate diagonal is amenable. -/
theorem IsApproximateDiagonal.isAmenable [ProperSpace 𝕜] [CompleteSpace A]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (h : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ hL hR hLR D hD ↦ h.exists_eq_dualAction_sub_dualAction hC hL hR hLR D hD

variable (𝕜) in
/-- The base field, with the diagonal `1 ⊗ 1`, is amenable over itself. -/
theorem isAmenable_self [ProperSpace 𝕜] : IsAmenable 𝕜 𝕜 :=
  (isApproximateDiagonal_pure_one_tmul_one 𝕜).isAmenable (C := 1) <|
    eventually_pure.2 <| (norm_coe_tmul_le _ _).trans (by simp)

end Amenable

end TauCeti
