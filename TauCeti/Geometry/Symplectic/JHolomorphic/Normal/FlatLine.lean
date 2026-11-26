/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FlatLine
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Connection
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
public import TauCeti.Geometry.Symplectic.Manifold.Quotient
public import TauCeti.Geometry.Symplectic.Prod.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent

/-!
# The coupling form of a flat normal line over a torus

Let `L ⊆ ℂ` be a full lattice and `ψ : L → S¹` a unitary character. The flat line `N` of holonomy
`ψ` over the torus `C = ℂ / L` (`TauCeti.FlatLine ψ`) is the orbit space of `ℂ × ℂ` under
`ω +ᵥ (z, v) = (z + ω, ψ ω v)`, a complex manifold of dimension two. It is the model of the normal
bundle of an embedded square-zero torus in Taubes's analysis of pseudoholomorphic curves in
symplectic four-manifolds, and when `ψ` has infinite order its only compact holomorphic curves lie
on the zero section (`TauCeti.FlatLine.exists_eq_mk_zero_of_mdifferentiable`).

Taubes normalizes the symplectic form near such a torus to the **coupling form**

`ω_N = π^* ω_C + d((|v|² / 2) (dθ + A))`

of a flat unitary connection `d + i A` on the normal line, where `ω_C` is an area form on the torus
and `v = |v| e^(iθ)` is the fibre coordinate (`TauCeti.normalCouplingForm`, Sternberg's minimal
coupling form). On the cover `ℂ × ℂ` the holonomy of the flat line is carried by the deck
transformations, and the connection is the trivial connection `d`, so `A = 0`. With the area form
`ω_ℂ(u, w) = Im (conj u w)` of `ℂ` on the base, the coupling form of the cover is then the
constant form

`ω_ℂ ⊕ ω_ℂ`,  `((u₁, u₂), (w₁, w₂)) ↦ Im (conj u₁ w₁) + Im (conj u₂ w₂)`

(`TauCeti.FlatLine.eval₂_couplingForm_mfderiv_mk_eq_normalCouplingForm`). A deck transformation
fixes the base direction and multiplies the fibre direction by the unit complex number `ψ ω`,
which preserves `ω_ℂ` (`TauCeti.FlatLine.mpullback_vadd_constSmooth`). So the form descends to the
flat line: **the coupling form of the flat line** `TauCeti.FlatLine.couplingForm ψ` is the unique
two-form on `N` pulling back to `ω_ℂ ⊕ ω_ℂ` along the orbit projection
(`TauCeti.FlatLine.eq_couplingForm_iff`). It is

* symplectic (`TauCeti.FlatLine.isSymplectic_couplingForm`);
* compatible with the complex structure of `N`
  (`TauCeti.FlatLine.compatible_couplingForm`), because the orbit projection is holomorphic and
  `ω_ℂ ⊕ ω_ℂ` is compatible with multiplication by `i`; compatibility descends along surjective
  local diffeomorphisms (`TauCeti.SmoothAlmostComplexStructure.compatible_descend_iff`);
* hence Kähler for that complex structure (`TauCeti.FlatLine.isKahler_couplingForm`).

So `(N, ω_N)` with its complex structure is a Kähler surface: the integrable compatible structure
near the torus that the normal model provides. The base carries the area form of `ℂ`.

## Main definitions

* `TauCeti.FlatLine.couplingForm ψ`: the coupling form of the flat line of holonomy `ψ`.

## Main results

* `TauCeti.FlatLine.mpullback_mk_couplingForm`, `TauCeti.FlatLine.eq_couplingForm_iff`: it is the
  unique two-form whose pullback to `ℂ × ℂ` is `ω_ℂ ⊕ ω_ℂ`.
* `TauCeti.FlatLine.eval₂_couplingForm_mfderiv_mk_eq_normalCouplingForm`: that pullback is the
  coupling form `π^* ω_ℂ + d((|v|² / 2) dθ)` of the trivial connection.
* `TauCeti.FlatLine.isSymplectic_couplingForm`, `TauCeti.FlatLine.compatible_couplingForm`,
  `TauCeti.FlatLine.isKahler_couplingForm`: it is a Kähler form for the complex structure of the
  flat line.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (square-zero tori and the flat model of their normal bundles).
* S. Sternberg, *Minimal coupling and the symplectic mechanics of a classical particle in the
  presence of a Yang–Mills field*, Proc. Nat. Acad. Sci. U.S.A. 74 (1977), 5253–5254.
-/

public noncomputable section

open Complex Function
open scoped Manifold ContDiff

namespace TauCeti

namespace FlatLine

open SmoothAlmostComplexStructure

variable {L : Submodule ℤ ℂ} {ψ : AddChar L Circle}

/-- The real-linear map of `ℂ × ℂ` that fixes the base direction and multiplies the fibre
direction by the holonomy `ψ γ` of a lattice vector `γ`. -/
private def holonomyCLM (γ : FlatLineLattice ψ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  (ContinuousLinearMap.fst ℝ ℂ ℂ).prod
    ((ContinuousLinearMap.mul ℝ ℂ (ψ (FlatLineLattice.toLattice ψ γ))).comp
      (ContinuousLinearMap.snd ℝ ℂ ℂ))

@[simp]
private theorem holonomyCLM_apply (γ : FlatLineLattice ψ) (v : ℂ × ℂ) :
    holonomyCLM γ v = (v.1, ψ (FlatLineLattice.toLattice ψ γ) * v.2) :=
  rfl

/-- The differential of the action of a lattice vector `γ` on `ℂ × ℂ` fixes the base direction and
multiplies the fibre direction by the holonomy `ψ γ`. -/
private theorem mfderiv_vadd (γ : FlatLineLattice ψ) (p : ℂ × ℂ) :
    mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ) (γ +ᵥ · : ℂ × ℂ → ℂ × ℂ) p = holonomyCLM γ := by
  -- The action is this real-linear map followed by a translation.
  have h : (γ +ᵥ · : ℂ × ℂ → ℂ × ℂ) =
      fun q ↦ holonomyCLM γ q + (((FlatLineLattice.toLattice ψ γ : L) : ℂ), 0) := by
    funext q
    simp
  rw [h]
  exact (ContinuousLinearMap.hasFDerivAt _ |>.add_const _).hasMFDerivAt.mfderiv

/-- **The holonomy preserves the flat form.** Each lattice vector acts on `ℂ × ℂ` by a
symplectomorphism of `ω_ℂ ⊕ ω_ℂ`: its differential fixes the base direction and multiplies the
fibre direction by the unit complex number `ψ γ`, which preserves the area form of `ℂ`. -/
theorem mpullback_vadd_constSmooth (γ : FlatLineLattice ψ) :
    SmoothForm.mpullback (γ +ᵥ ·) (contMDiff_const_vadd γ)
        (stdComplexSymplecticForm.prod stdComplexSymplecticForm).constSmooth =
      (stdComplexSymplecticForm.prod stdComplexSymplecticForm).constSmooth := by
  have key (v w : ℂ × ℂ) :
      stdComplexSymplecticForm.prod stdComplexSymplecticForm (holonomyCLM γ v) (holonomyCLM γ w) =
        stdComplexSymplecticForm.prod stdComplexSymplecticForm v w := by
    simp only [holonomyCLM_apply, SymplecticForm.prod_apply, stdComplexSymplecticForm_mul_mul,
      Circle.norm_coe, one_pow, one_mul]
  refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, mfderiv_vadd]
  exact (SymplecticForm.constSmooth_apply _ _ _ _).trans
    ((key v w).trans (SymplecticForm.constSmooth_apply _ _ _ _).symm)

variable [DiscreteTopology L]

variable (ψ) in
/-- **The coupling form of the flat line** of holonomy `ψ`: the descent to the flat line of the
constant form `ω_ℂ ⊕ ω_ℂ` on `ℂ × ℂ`, `((u₁, u₂), (w₁, w₂)) ↦ Im (conj u₁ w₁) + Im (conj u₂ w₂)`,
which the holonomy preserves. It is the coupling form `π^* ω_ℂ + d((|v|² / 2) dθ)` of the flat
connection, read on the cover
(`TauCeti.FlatLine.eval₂_couplingForm_mfderiv_mk_eq_normalCouplingForm`), and a Kähler form for
the complex structure of the flat line (`TauCeti.FlatLine.isKahler_couplingForm`). -/
def couplingForm : SmoothTwoForm 𝓘(ℝ, ℂ × ℂ) (FlatLine ψ) :=
  SmoothForm.addDescend (stdComplexSymplecticForm.prod stdComplexSymplecticForm).constSmooth
    mpullback_vadd_constSmooth

/-- The coupling form pulls back to `ω_ℂ ⊕ ω_ℂ` along the orbit projection `ℂ × ℂ → N`. -/
@[simp]
theorem mpullback_mk_couplingForm :
    SmoothForm.mpullback (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ)))
        isLocalDiffeomorph_addQuotientMk.contMDiff (couplingForm ψ) =
      (stdComplexSymplecticForm.prod stdComplexSymplecticForm).constSmooth :=
  SmoothForm.mpullback_addQuotientMk_addDescend

/-- The coupling form is the unique two-form on the flat line whose pullback to `ℂ × ℂ` is
`ω_ℂ ⊕ ω_ℂ`. -/
theorem eq_couplingForm_iff {σ : SmoothTwoForm 𝓘(ℝ, ℂ × ℂ) (FlatLine ψ)} :
    σ = couplingForm ψ ↔
      SmoothForm.mpullback (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ)))
          isLocalDiffeomorph_addQuotientMk.contMDiff σ =
        (stdComplexSymplecticForm.prod stdComplexSymplecticForm).constSmooth :=
  SmoothForm.eq_addDescend_iff

/-- The coupling form in the coordinates of the cover: on the images of tangent vectors `u` and
`w` at a point of `ℂ × ℂ`, it is `ω_ℂ(u₁, w₁) + ω_ℂ(u₂, w₂)`. -/
theorem eval₂_couplingForm_mfderiv_mk (p u w : ℂ × ℂ) :
    (couplingForm ψ).eval₂ (Quotient.mk _ p)
        (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p u)
        (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p w) =
      stdComplexSymplecticForm u.1 w.1 + stdComplexSymplecticForm u.2 w.2 := by
  have h := SmoothForm.eval₂_mpullback _ isLocalDiffeomorph_addQuotientMk.contMDiff
    (couplingForm ψ) p u w
  rw [mpullback_mk_couplingForm] at h
  rw [← h, SymplecticForm.constSmooth_apply, SymplecticForm.prod_apply]

/-- **The coupling form is Taubes's coupling form of the flat connection.** On the cover
`ℂ × ℂ`, where the holonomy is carried by the deck transformations and the connection is
trivial, the coupling form of the flat line is the coupling form `π^* ω₀ + d((|v|² / 2) dθ)`
(`TauCeti.normalCouplingForm ω₀ 0`) of a base form `ω₀` equal to the area form of `ℂ`. -/
theorem eval₂_couplingForm_mfderiv_mk_eq_normalCouplingForm {ω₀ : ℂ → ℂ [⋀^Fin 2]→L[ℝ] ℝ}
    (hω₀ : ∀ z v v', ω₀ z ![v, v'] = stdComplexSymplecticForm v v') (p u w : ℂ × ℂ) :
    (couplingForm ψ).eval₂ (Quotient.mk _ p)
        (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p u)
        (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p w) =
      normalCouplingForm ω₀ 0 p ![u, w] := by
  rw [eval₂_couplingForm_mfderiv_mk, normalCouplingForm_apply_eq_normalCovariantDeriv (A := 0)
    (differentiableAt_const 0), hω₀]
  simp [normalCovariantDeriv_def, Pi.zero_def, ContinuousAlternatingMap.extDeriv_const]

/-- **The coupling form of the flat line is symplectic.** -/
theorem isSymplectic_couplingForm : (couplingForm ψ).IsSymplectic :=
  SmoothTwoForm.isSymplectic_addDescend_iff.2 (SymplecticForm.isSymplectic_constSmooth _)

/-- **The coupling form is compatible with the complex structure of the flat line**: it is
invariant under multiplication by `i` on the tangent spaces and positive on every complex line. -/
theorem compatible_couplingForm :
    (couplingForm ψ).Compatible (ofComplexManifold (ℂ × ℂ) (FlatLine ψ)) := by
  have hq := isLocalDiffeomorph_addQuotientMk (G := FlatLineLattice ψ) (I := 𝓘(ℝ, ℂ × ℂ))
    (M := ℂ × ℂ) (n := ∞)
  -- The structure of `ℂ × ℂ` is the pullback of that of the flat line, since the orbit
  -- projection is holomorphic and so its real differential commutes with `i`.
  have hJ : ofComplexManifold (ℂ × ℂ) (ℂ × ℂ) =
      localPullback hq (ofComplexManifold (ℂ × ℂ) (FlatLine ψ)) :=
    (eq_localPullback_iff hq _ _).2 fun p v ↦
      ((isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ, ℂ × ℂ)) (n := ⊤)).contMDiff.mdifferentiable
        (by simp) p).mfderiv_ofComplexManifold_apply v
  -- Compatibility with the descent of that pullback is checked upstairs, against `ω_ℂ ⊕ ω_ℂ`.
  rw [← descend_localPullback hq (ofComplexManifold (ℂ × ℂ) (FlatLine ψ)) Quotient.mk_surjective,
    compatible_descend_iff, ← hJ, mpullback_mk_couplingForm, ofComplexManifold_self_eq_constSmooth,
    SymplecticForm.compatible_constSmooth_iff]
  -- On `ℂ × ℂ`, multiplication by `i` is the product of the structures of the factors.
  have h : AlmostComplexStructure.ofComplexModule (ℂ × ℂ) =
      (AlmostComplexStructure.ofComplexModule ℂ).prod (AlmostComplexStructure.ofComplexModule ℂ) :=
    AlmostComplexStructure.ext fun p ↦ by simp [Prod.smul_def]
  rw [h]
  exact SymplecticForm.prod_compatible stdComplexSymplecticForm_compatible
    stdComplexSymplecticForm_compatible

/-- **The flat line is a Kähler surface**: its coupling form is closed and compatible with its
complex structure, which is integrable. -/
theorem isKahler_couplingForm :
    (couplingForm ψ).IsKahler (ofComplexManifold (ℂ × ℂ) (FlatLine ψ)) :=
  SmoothTwoForm.isKahler_ofComplexManifold_iff.2
    ⟨isSymplectic_couplingForm.isClosed, compatible_couplingForm⟩

end FlatLine

end TauCeti
