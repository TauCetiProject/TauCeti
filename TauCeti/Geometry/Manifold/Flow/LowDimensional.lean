/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.RestPoint
public import TauCeti.Geometry.Manifold.Flow.ReturnDerivative
public import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Closed orbits of vector fields in dimensions zero and one

A closed orbit of a vector field `v` through a point `p` returning to itself at time `T` is
*nondegenerate* when, for a section `{g = g p}` transverse to `v` at `p`, `1` is not an eigenvalue
of the linearized return map `TauCeti.returnDerivative v g T p`; by
`TauCeti.hasEigenvalue_returnDerivative_iff` this does not depend on the section or on the point
of the orbit. The return times of `p` include all positive multiples of its period, so this
covers every positive iterate of a primitive closed orbit. In general nondegeneracy of all closed
orbits only holds for generic fields, and needs a perturbation. This file treats the two
dimensions in which it holds for every field, with no perturbation.

**Dimension zero.** On a manifold modelled on a space of dimension `0` every tangent vector
vanishes, so every point is a rest point and every trajectory is constant
(`TauCeti.flowOf_eq_self_of_finrank_eq_zero`): there is no nonstationary closed orbit, and no
section is transverse to the field.

**Dimension one.** On a manifold modelled on a line, a section through a nonstationary point `p`
is transverse to `v` when `dg_p (v p) ≠ 0`, and then its tangent space `ker dg_p` is zero
(`TauCeti.ker_mvfderiv_eq_bot_of_finrank_eq_one`). The linearized return map takes values in that
tangent space, so it vanishes (`TauCeti.returnDerivative_eq_zero_of_finrank_eq_one`) and has no
nonzero eigenvalue (`TauCeti.not_hasEigenvalue_returnDerivative_of_finrank_eq_one`): every closed
orbit, and every positive iterate of it, is nondegenerate. The normal return derivative acts on
the zero space, so it has no eigenvalue at all
(`TauCeti.not_hasEigenvalue_normalReturnDerivative_of_finrank_eq_one`), and `det (1 - N) = 1` by
the convention that the determinant of an endomorphism of the zero space is `1`
(`TauCeti.det_one_sub_normalReturnDerivative_of_finrank_eq_one`). Correspondingly the derivative
`DΦ_T` of the time-`T` map at `p`, the monodromy of the orbit, is the identity
(`TauCeti.mfderiv_flowOf_apply_of_finrank_eq_one`): it fixes `v p`, which spans `T_p M`. Its only
Floquet multiplier is the trivial multiplier `1` of the flow direction. On a smooth manifold every
nonstationary point has a transverse section, so every closed orbit of a `C¹` field is
nondegenerate in the sense used by `TauCeti.Geometry.Manifold.Flow.Persistence`
(`TauCeti.exists_not_hasEigenvalue_one_returnDerivative_of_finrank_eq_one`).

## Main results

* `TauCeti.flowOf_eq_self_of_finrank_eq_zero`: in dimension zero every trajectory is constant.
* `TauCeti.returnDerivative_eq_zero_of_finrank_eq_one`: in dimension one the linearized return
  map of a closed orbit vanishes.
* `TauCeti.not_hasEigenvalue_returnDerivative_of_finrank_eq_one`: in dimension one every closed
  orbit, at every return time, is nondegenerate.
* `TauCeti.det_one_sub_normalReturnDerivative_of_finrank_eq_one`: in dimension one
  `det (1 - N) = 1` for the normal return derivative `N`.
* `TauCeti.mfderiv_flowOf_apply_of_finrank_eq_one`: in dimension one the monodromy of a closed
  orbit is the identity.
* `TauCeti.exists_not_hasEigenvalue_one_returnDerivative_of_finrank_eq_one`: in dimension one
  every closed orbit through a nonstationary point is nondegenerate for some transverse section.

## References

* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations
  **3** (1967), 214–227 (closed-return genericity of vector fields).
* G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, AMS Graduate Studies in
  Mathematics **140**, 2012, §12.2 (Poincaré maps and Floquet multipliers of periodic orbits).
-/

public section

open Module Manifold
open scoped ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {g : M → ℝ} {T : ℝ} {p : M}

/-! ### Dimension zero -/

/-- **In dimension zero every trajectory is constant.** On a manifold modelled on a space of
dimension `0`, every vector field vanishes, so every time-`t` map of its flow fixes every point.
In particular there is no nonstationary closed orbit. -/
theorem flowOf_eq_self_of_finrank_eq_zero (hE : finrank ℝ E = 0)
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (t : ℝ) (p : M) :
    flowOf v t p = p :=
  haveI : Subsingleton E := finrank_zero_iff.1 hE
  flowOf_eq_self_of_eq_zero hv (Subsingleton.elim (α := E) _ _) t

/-! ### Dimension one -/

section DimensionOne

variable (hE : finrank ℝ E = 1)
include hE

omit [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- **In dimension one a transverse section has zero tangent space.** If `dg_p (v p) ≠ 0` on a
manifold modelled on a line, then `dg_p` is a nonzero linear form between lines, hence injective. -/
theorem ker_mvfderiv_eq_bot_of_finrank_eq_one (hgv : mvfderiv I g p (v p) ≠ 0) :
    LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ) = ⊥ :=
  LinearMap.ker_eq_bot.2 <|
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hE.trans (finrank_self ℝ).symm)).2 <|
      LinearMap.surjective_of_ne_zero fun h0 ↦ hgv (LinearMap.congr_fun h0 (v p))

/-- **In dimension one the normal return derivative has no eigenvalue.** If `p` returns to itself
at time `T` on a manifold modelled on a line, the normal return derivative of a section transverse
to `v` at `p` acts on the zero space. -/
theorem not_hasEigenvalue_normalReturnDerivative_of_finrank_eq_one
    (hgv : mvfderiv I g p (v p) ≠ 0)
    {h : LinearMap.range (returnDerivative v g T p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} (μ : ℝ) :
    ¬(normalReturnDerivative v g T p h).HasEigenvalue μ := by
  intro hμ
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 : (w : TangentSpace I p) = 0 := by
    simpa [ker_mvfderiv_eq_bot_of_finrank_eq_one hE hgv] using w.property
  exact hw.2 (Subtype.ext hw0)

/-- **In dimension one `det (1 - N) = 1`.** If `p` returns to itself at time `T` on a manifold
modelled on a line, the normal return derivative `N` of a section transverse to `v` at `p` acts on
the zero space, so `det (1 - N)` is the empty determinant `1`. -/
theorem det_one_sub_normalReturnDerivative_of_finrank_eq_one (hgv : mvfderiv I g p (v p) ≠ 0)
    {h : LinearMap.range (returnDerivative v g T p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    LinearMap.det (1 - normalReturnDerivative v g T p h) = 1 :=
  LinearMap.det_eq_one_of_finrank_eq_zero
    (Submodule.finrank_eq_zero.2 (ker_mvfderiv_eq_bot_of_finrank_eq_one hE hgv)) _

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hT : (T, p) ∈ flowDomain v) (hp : flowOf v T p = p)
include hv hT hp

/-- **In dimension one the linearized return map vanishes.** If `p` returns to itself at time `T`
on a manifold modelled on a line, the linearized return map of a section transverse to `v` at `p`
is zero: it takes values in the tangent space of the section, which is zero. -/
theorem returnDerivative_eq_zero_of_finrank_eq_one (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (v p) ≠ 0) :
    returnDerivative v g T p = 0 :=
  LinearMap.range_eq_bot.1 <| eq_bot_iff.2 <|
    (range_returnDerivative_le_ker hv hT hp hg hgv).trans
      (ker_mvfderiv_eq_bot_of_finrank_eq_one hE hgv).le

/-- **In dimension one every closed orbit is nondegenerate.** If `p` returns to itself at time `T`
on a manifold modelled on a line, the linearized return map of a section transverse to `v` at `p`
has no nonzero eigenvalue; in particular `1` is not an eigenvalue. Every positive multiple of a
return time is a return time, so this holds for every positive iterate of the orbit. -/
theorem not_hasEigenvalue_returnDerivative_of_finrank_eq_one (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (v p) ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    ¬(returnDerivative v g T p).HasEigenvalue μ := by
  intro h
  obtain ⟨w, hw⟩ := h.exists_hasEigenvector
  have hμw : μ • w = 0 := by
    rw [← hw.apply_eq_smul, returnDerivative_eq_zero_of_finrank_eq_one hE hv hT hp hg hgv,
      LinearMap.zero_apply]
  exact hw.2 ((smul_eq_zero.1 hμw).resolve_left hμ)

/-- **In dimension one the monodromy of a closed orbit is the identity.** If a nonstationary point
`p` returns to itself at time `T` on a manifold modelled on a line, the derivative at `p` of the
time-`T` map of the flow fixes every tangent vector: it fixes `v p`, which spans `T_p M`. -/
theorem mfderiv_flowOf_apply_of_finrank_eq_one (hvp : v p ≠ 0) (w : TangentSpace I p) :
    -- The derivative lands in the tangent space at `flowOf v T p`, which is `p` only
    -- propositionally; both tangent spaces are the model space `E`, so the equation is well typed.
    mfderiv I I (flowOf v T) p w = w := by
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' (V := TangentSpace I p) (v p) hvp).1 hE w
  rw [map_smul, mfderiv_flowOf_apply_self hv hT]
  -- As above, `congrArg v hp` is an equation of vectors in `E`.
  exact congrArg (c • ·) (congrArg v hp)

/-- **In dimension one every closed orbit is nondegenerate for some transverse section.** On a
smooth manifold modelled on a line, if a nonstationary point `p` returns to itself at time `T`
under the flow of a `C¹` field `v`, there is a section through `p` transverse to `v` whose
linearized return map does not have the eigenvalue `1`. This is the nondegeneracy condition of
`TauCeti.isOpen_setOf_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative`. -/
theorem exists_not_hasEigenvalue_one_returnDerivative_of_finrank_eq_one [IsManifold I ∞ M]
    (hvp : v p ≠ 0) :
    ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g p ∧ mvfderiv I g p (v p) ≠ 0 ∧
      ¬(returnDerivative v g T p).HasEigenvalue 1 := by
  obtain ⟨g, hg, hgv⟩ := exists_contMDiff_mvfderiv_apply_ne_zero (I := I) p hvp
  have hg1 : ContMDiffAt I 𝓘(ℝ) 1 g p := (hg.of_le (by norm_cast)).contMDiffAt
  exact ⟨g, hg1, hgv,
    not_hasEigenvalue_returnDerivative_of_finrank_eq_one hE hv hT hp hg1 hgv one_ne_zero⟩

end DimensionOne

end TauCeti
