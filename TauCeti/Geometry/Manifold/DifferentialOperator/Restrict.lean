/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol
import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Restricting differential operators to open subsets

Let `M` be a finite-dimensional Hausdorff smooth manifold and `U ⊆ M` an open subset. A
differential operator `D` of order at most `m` on `C^∞(M)`, in Grothendieck's sense of iterated
commutators with multiplication operators (`TauCeti.differentialOperators`), is local: `(D g)(x)`
only depends on the germ of `g` at `x` (`TauCeti.differentialOperators_apply_eq_of_eventuallyEq`).
Every smooth function `f` on `U` agrees near each point `x ∈ U` with the restriction of a smooth
function `g` on `M`, so

`(D|_U f)(x) = (D g)(x)`

is well defined. This gives the restriction `D|_U`, a differential operator of order at most `m` on
`C^∞(U)` (`TopologicalSpace.Opens.restrictDifferentialOperators`). It is the unique operator on
`U` with `D|_U (g|_U) = (D g)|_U` for all `g ∈ C^∞(M)`
(`TopologicalSpace.Opens.eq_coe_restrictDifferentialOperators`). No continuity of `D` is assumed,
and boundary points are allowed.

Restriction is linear in `D`, commutes with composition and with commutators by multiplication
operators, and preserves the principal symbol: at an interior point `x ∈ U` the principal symbol
of `D|_U` is that of `D`, the cotangent spaces of `U` and `M` at `x` being identified through the
tangent spaces (`TauCeti.Manifold.tangentSpaceOpenEquiv`). A derivation of `C^∞(M)` restricts to a
derivation of `C^∞(U)` (`TopologicalSpace.Opens.restrictDerivation`), and on a boundaryless
manifold the vector field of the restricted derivation is the restriction of its vector field
(`Derivation.vectorField_restrictDerivation`).

Restriction is how the global algebraic operators on `M` are compared with local coordinate
expressions: on a chart domain `U` the restriction is transported to the chart image, where
differential operators are the finite coordinate expressions `∑_{|α| ≤ m} c_α ∂^α`.

## Main definitions

* `TopologicalSpace.Opens.restrictDifferentialOperators U m`: restriction `D ↦ D|_U` of the
  differential operators of order at most `m` on `C^∞(M)` to the open subset `U`, as a linear map.
* `TopologicalSpace.Opens.restrictDerivation U δ`: the restriction of a derivation of `C^∞(M)`.

## Main results

* `TopologicalSpace.Opens.restrictDifferentialOperators_apply_of_eventuallyEq`:
  `(D|_U f)(x) = (D g)(x)` for any `g` whose restriction agrees with `f` near `x`.
* `TopologicalSpace.Opens.restrictDifferentialOperators_apply_restrict`:
  `D|_U (g|_U) = (D g)|_U`.
* `TopologicalSpace.Opens.eq_coe_restrictDifferentialOperators`: uniqueness of the restriction.
* `TopologicalSpace.Opens.restrictDifferentialOperators_comp`: restriction commutes with
  composition.
* `TauCeti.smulCommutator_restrictDifferentialOperators`,
  `TauCeti.commutatorSymbol_restrictDifferentialOperators_apply_restrict`: restriction commutes with
  commutators and with the commutator symbol.
* `TauCeti.smoothPrincipalSymbol_restrictDifferentialOperators`: restriction preserves the
  principal symbol.
* `Derivation.vectorField_restrictDerivation`: the vector field of a restricted derivation.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§1.3–1.6 (germs and localization of smooth functions) and §19 (local operators).
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open Filter TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (U : Opens M)

/-! ### Germs on an open subset -/

/-- The value at `x ∈ U` of the restriction of `D` to `U` on `f`: the value at `x` of `D` on a
smooth function on `M` whose restriction agrees with `f` near `x`. -/
private def restrictValue (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) (f : C^∞⟮I, U; ℝ⟯) (x : U) : ℝ :=
  D (f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)).choose x

variable {U} {m k : ℕ}

private theorem restrictValue_eq {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    {f : C^∞⟮I, U; ℝ⟯} {x : U} {g : C^∞⟮I, M; ℝ⟯} (hg : (g : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] f) :
    restrictValue U D f x = D g x := by
  refine differentialOperators_apply_eq_of_eventuallyEq hD ?_
  -- Both functions agree with `f` near `x` in `U`, and `𝓝 x` in `M` is the image of `𝓝 x` in `U`.
  rw [← U.isOpenEmbedding'.map_nhds_eq x]
  exact eventuallyEq_map.2 <|
    (f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)).choose_spec.trans
      hg.symm

private theorem contMDiff_restrictValue {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (f : C^∞⟮I, U; ℝ⟯) : ContMDiff I 𝓘(ℝ) ∞ (restrictValue U D f) := fun x ↦ by
  obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
  refine ((D g).contMDiff.comp contMDiff_subtype_val).contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hg.eventuallyEq_nhds] with y hy
  exact restrictValue_eq hD hy

/-- The restriction of `D` applied to `f`, as a smooth function on `U`. -/
private def restrictFun {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (f : C^∞⟮I, U; ℝ⟯) : C^∞⟮I, U; ℝ⟯ :=
  ⟨restrictValue U D f, contMDiff_restrictValue hD f⟩

private theorem restrictFun_apply {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (f : C^∞⟮I, U; ℝ⟯) (x : U) : restrictFun hD f x = restrictValue U D f x :=
  (rfl)

/-- The restriction of a differential operator as a linear map on `C^∞(U)`. -/
private def restrictLinearMap {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯ where
  toFun := restrictFun hD
  map_add' f f' := by
    ext x
    obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
    obtain ⟨g', hg'⟩ := f'.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
    have hsum : ((g + g' : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] (f + f' : C^∞⟮I, U; ℝ⟯) :=
      hg.add hg'
    rw [ContMDiffMap.coe_add, Pi.add_apply, restrictFun_apply, restrictFun_apply,
      restrictFun_apply, restrictValue_eq hD hsum, restrictValue_eq hD hg,
      restrictValue_eq hD hg', map_add, ContMDiffMap.coe_add, Pi.add_apply]
  map_smul' c f := by
    ext x
    obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
    have hsmul : ((c • g : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] (c • f : C^∞⟮I, U; ℝ⟯) :=
      hg.const_smul c
    rw [RingHom.id_apply, ContMDiffMap.coe_smul, Pi.smul_apply, restrictFun_apply,
      restrictFun_apply, restrictValue_eq hD hsmul, restrictValue_eq hD hg, map_smul,
      ContMDiffMap.coe_smul, Pi.smul_apply]

/-- A function on `U` in the `n`-th power of the vanishing ideal at `x` agrees near `x` with the
restriction of a function on `M` in the `n`-th power of the vanishing ideal at `x`. -/
private theorem exists_mem_pow_eventuallyEq {x : U} {n : ℕ} {h : C^∞⟮I, U; ℝ⟯}
    (hh : h ∈ smoothVanishingIdeal I x ^ n) :
    ∃ g ∈ smoothVanishingIdeal I (x : M) ^ n, (g : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] h := by
  induction n generalizing h with
  | zero =>
    obtain ⟨g, hg⟩ := h.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
    exact ⟨g, by simp, hg⟩
  | succ n ih =>
    rw [pow_succ'] at hh
    refine Submodule.mul_induction_on hh (fun a ha b hb ↦ ?_) fun h₁ h₂ ↦ ?_
    · obtain ⟨g, hg⟩ := a.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
      obtain ⟨g', hg', hbg⟩ := ih hb
      have hgx : g ∈ smoothVanishingIdeal I (x : M) := by
        rw [mem_smoothVanishingIdeal_iff]
        exact hg.eq_of_nhds.trans (mem_smoothVanishingIdeal_iff.1 ha)
      exact ⟨g * g', pow_succ' (smoothVanishingIdeal I (x : M)) n ▸ Ideal.mul_mem_mul hgx hg',
        hg.mul hbg⟩
    · rintro ⟨g₁, hg₁, hgh₁⟩ ⟨g₂, hg₂, hgh₂⟩
      exact ⟨g₁ + g₂, add_mem hg₁ hg₂, hgh₁.add hgh₂⟩

private theorem restrictLinearMap_mem {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    restrictLinearMap (U := U) hD ∈
      differentialOperators ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ m := by
  rw [mem_differentialOperators_iff_forall_apply_mem_smul_top
    (fun x : U ↦ (ContMDiffMap.evalAlgHom x : C^∞⟮I, U; ℝ⟯ →ₐ[ℝ] ℝ))
    ContMDiffMap.eq_zero_of_forall_mem_ker_evalAlgHom_smul_top]
  intro x h hh
  simp only [ker_evalAlgHom_eq_smoothVanishingIdeal, Ideal.smul_eq_mul, Ideal.mul_top] at hh ⊢
  obtain ⟨g, hg, hgh⟩ := exists_mem_pow_eventuallyEq hh
  have hDg := apply_mem_smul_top_of_mem_pow_smul_top hD _ (x := g) (by simpa using hg)
  rw [Ideal.smul_eq_mul, Ideal.mul_top, mem_smoothVanishingIdeal_iff] at hDg
  rw [mem_smoothVanishingIdeal_iff]
  exact (restrictValue_eq hD hgh).trans hDg

/-! ### Restriction of differential operators -/

variable (U m) in
/-- **Restriction of differential operators to an open subset.** For a differential operator `D`
of order at most `m` on `C^∞(M)` and an open subset `U`, the restriction `D|_U` is the
differential operator of order at most `m` on `C^∞(U)` whose value on `f` at `x ∈ U` is
`(D g)(x)` for any smooth `g` on `M` agreeing with `f` near `x`
(`TopologicalSpace.Opens.restrictDifferentialOperators_apply_of_eventuallyEq`). It is
characterized by `D|_U (g|_U) = (D g)|_U`
(`TopologicalSpace.Opens.eq_coe_restrictDifferentialOperators`). -/
def _root_.TopologicalSpace.Opens.restrictDifferentialOperators :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m →ₗ[ℝ]
      differentialOperators ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ m where
  toFun D := ⟨restrictLinearMap D.2, restrictLinearMap_mem D.2⟩
  map_add' D₁ D₂ := by
    ext f x
    obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
    exact (restrictValue_eq (D₁ + D₂).2 hg).trans
      (congrArg₂ (· + ·) (restrictValue_eq D₁.2 hg) (restrictValue_eq D₂.2 hg)).symm
  map_smul' c D := by
    ext f x
    obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
    exact (restrictValue_eq (c • D).2 hg).trans
      (congrArg (c * ·) (restrictValue_eq D.2 hg)).symm

/-- **The values of a restricted operator.** If the restriction of `g ∈ C^∞(M)` agrees with
`f ∈ C^∞(U)` near `x`, then `(D|_U f)(x) = (D g)(x)`. -/
theorem _root_.TopologicalSpace.Opens.restrictDifferentialOperators_apply_of_eventuallyEq
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    {f : C^∞⟮I, U; ℝ⟯} {x : U} {g : C^∞⟮I, M; ℝ⟯} (hg : (g : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] f) :
    (U.restrictDifferentialOperators m D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) f x =
      (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) g x :=
  restrictValue_eq D.2 hg

/-- The restriction of `D` sends the restriction of `g` to the restriction of `D g`. -/
@[simp]
theorem _root_.TopologicalSpace.Opens.restrictDifferentialOperators_apply_restrict
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) (g : C^∞⟮I, M; ℝ⟯) :
    (U.restrictDifferentialOperators m D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) (g.restrict U) =
      ((D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) g).restrict U := by
  ext x
  rw [ContMDiffMap.restrict_apply]
  exact Opens.restrictDifferentialOperators_apply_of_eventuallyEq D
    (EventuallyEq.of_eq (ContMDiffMap.coe_restrict g U).symm)

/-- **Uniqueness of the restriction.** A differential operator `P` of any order on `C^∞(U)` with
`P (g|_U) = (D g)|_U` for every `g ∈ C^∞(M)` is the restriction of `D`. -/
theorem _root_.TopologicalSpace.Opens.eq_coe_restrictDifferentialOperators
    {P : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ k)
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (h : ∀ g : C^∞⟮I, M; ℝ⟯, P (g.restrict U) =
      ((D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) g).restrict U) :
    P = U.restrictDifferentialOperators m D := by
  ext f x
  obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
  rw [Opens.restrictDifferentialOperators_apply_of_eventuallyEq D hg,
    differentialOperators_apply_eq_of_eventuallyEq hP (g := g.restrict U)
      (hg.symm.trans (EventuallyEq.of_eq (ContMDiffMap.coe_restrict g U).symm)), h g,
    ContMDiffMap.restrict_apply]

/-- A differential operator on `C^∞(U)` is the restriction of `D` exactly when it sends the
restriction of every `g ∈ C^∞(M)` to the restriction of `D g`. -/
theorem _root_.TopologicalSpace.Opens.eq_restrictDifferentialOperators_iff
    {P : differentialOperators ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ m}
    {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m} :
    P = U.restrictDifferentialOperators m D ↔
      ∀ g : C^∞⟮I, M; ℝ⟯, (P : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) (g.restrict U) =
        ((D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) g).restrict U := by
  refine ⟨?_, fun h ↦ Subtype.ext (Opens.eq_coe_restrictDifferentialOperators P.2 D h)⟩
  rintro rfl g
  exact Opens.restrictDifferentialOperators_apply_restrict D g

/-- **Restriction commutes with composition.** The restriction of `D ∘ D'`, an operator of order
at most `m + k`, is the composition of the restrictions. -/
theorem _root_.TopologicalSpace.Opens.restrictDifferentialOperators_comp
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (D' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k) :
    (U.restrictDifferentialOperators (m + k)
        ⟨(D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∘ₗ (D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯),
          comp_mem_differentialOperators D.2 D'.2⟩ : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) =
      (U.restrictDifferentialOperators m D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) ∘ₗ
        (U.restrictDifferentialOperators k D' : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) :=
  (Opens.eq_coe_restrictDifferentialOperators
    (comp_mem_differentialOperators (U.restrictDifferentialOperators m D).2
      (U.restrictDifferentialOperators k D').2) _ fun g ↦ by simp).symm

/-- **Restriction commutes with commutators.** The commutator of `D|_U` with multiplication by
the restriction of `f` is the restriction of the commutator `[D, f]`. -/
theorem smulCommutator_restrictDifferentialOperators
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (m + 1))
    (f : C^∞⟮I, M; ℝ⟯) :
    smulCommutator ℝ (f.restrict U)
        (U.restrictDifferentialOperators (m + 1) D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) =
      (Opens.restrictDifferentialOperators (I := I) U m
        ⟨smulCommutator ℝ f D, smulCommutator_mem_differentialOperators D.2 f⟩ :
          C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) :=
  Opens.eq_coe_restrictDifferentialOperators
    (smulCommutator_mem_differentialOperators (U.restrictDifferentialOperators (m + 1) D).2 _) _
    fun g ↦ by
      simp only [smulCommutator_apply_apply, smul_eq_mul, ← ContMDiffMap.restrict_mul,
        Opens.restrictDifferentialOperators_apply_restrict, ContMDiffMap.restrict_sub]

/-- **Restriction commutes with the commutator symbol.** The iterated commutator of `D|_U` with
the restrictions of `f₁, …, fₘ`, applied to the restriction of `g`, is the restriction of the
iterated commutator `[⋯[D, f₁], …, fₘ] g`. -/
theorem commutatorSymbol_restrictDifferentialOperators_apply_restrict
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (f : Fin m → C^∞⟮I, M; ℝ⟯) (g : C^∞⟮I, M; ℝ⟯) :
    commutatorSymbol ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ m
        (U.restrictDifferentialOperators m D) (fun i ↦ (f i).restrict U) (g.restrict U) =
      (commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m D f g).restrict U := by
  induction m with
  | zero =>
    rw [commutatorSymbol_zero_apply, commutatorSymbol_zero_apply]
    exact Opens.restrictDifferentialOperators_apply_restrict D g
  | succ m ih =>
    rw [commutatorSymbol_succ_apply, commutatorSymbol_succ_apply, ← ih]
    exact congrArg (fun P ↦ commutatorSymbol ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ m P
      (fun i ↦ (f i.succ).restrict U) (g.restrict U))
      (Subtype.ext (smulCommutator_restrictDifferentialOperators D (f 0)))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- The differential at `x ∈ U` of the restriction of `f` is the differential of `f` at `x`,
composed with the identification of the tangent spaces of `U` and `M`. -/
private theorem mvfderiv_restrict (f : C^∞⟮I, M; ℝ⟯) (x : U) :
    mvfderiv I (f.restrict U) x =
      (mvfderiv I f x).comp (Manifold.tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap := by
  rw [ContMDiffMap.coe_restrict, mvfderiv_comp x (f.contMDiff.mdifferentiable (by simp) _)
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)), Manifold.mfderiv_subtype_val]

/-- **Restriction preserves the commutator symbol.** At an interior point `x ∈ U`, the commutator
symbol of `D|_U` on covectors `ηᵢ ∘ ι` is the commutator symbol of `D` on the covectors `ηᵢ`, where
`ι : T_x U ≃ T_x M` is the identification of the tangent spaces. -/
theorem smoothCommutatorSymbol_restrictDifferentialOperators {x : U}
    (hx : I.IsInteriorPoint (x : M))
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (η : Fin m → TangentSpace I (x : M) →L[ℝ] ℝ) :
    smoothCommutatorSymbol I (I.isInteriorPoint_iff_isInteriorPoint_val.mpr hx)
        (U.restrictDifferentialOperators m D)
        (fun i ↦ (η i).comp (Manifold.tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap) =
      smoothCommutatorSymbol I hx D η := by
  choose f _ hf using fun i ↦ exists_contMDiffMap_mvfderiv_eq (I := I) (x : M) (0 : ℝ) (η i)
  obtain rfl : (fun i ↦ mvfderiv I (f i) (x : M)) = η := funext hf
  have hone : (1 : C^∞⟮I, U; ℝ⟯) = (1 : C^∞⟮I, M; ℝ⟯).restrict U := by
    ext
    simp
  simp only [← mvfderiv_restrict]
  rw [smoothCommutatorSymbol_mvfderiv, smoothCommutatorSymbol_mvfderiv, hone,
    commutatorSymbol_restrictDifferentialOperators_apply_restrict, ContMDiffMap.restrict_apply]

/-- **Restriction preserves the principal symbol.** At an interior point `x ∈ U`, the principal
symbol of `D|_U` at `ξ ∘ ι` is the principal symbol of `D` at `ξ`, where `ι : T_x U ≃ T_x M` is the
identification of the tangent spaces. -/
theorem smoothPrincipalSymbol_restrictDifferentialOperators {x : U}
    (hx : I.IsInteriorPoint (x : M))
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (ξ : TangentSpace I (x : M) →L[ℝ] ℝ) :
    smoothPrincipalSymbol I (I.isInteriorPoint_iff_isInteriorPoint_val.mpr hx)
        (U.restrictDifferentialOperators m D)
        (ξ.comp (Manifold.tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap) =
      smoothPrincipalSymbol I hx D ξ := by
  rw [smoothPrincipalSymbol_def, smoothPrincipalSymbol_def,
    smoothCommutatorSymbol_restrictDifferentialOperators hx D fun _ ↦ ξ]

/-! ### Restriction of derivations -/

/-- The restriction of a derivation satisfies the Leibniz rule. -/
private theorem restrictDifferentialOperators_leibniz
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (a b : C^∞⟮I, U; ℝ⟯) :
    (Opens.restrictDifferentialOperators (I := I) U 1 ⟨δ, δ.mem_differentialOperators_one⟩ :
        C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) (a * b) =
      a • (Opens.restrictDifferentialOperators (I := I) U 1
          ⟨δ, δ.mem_differentialOperators_one⟩ : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) b +
        b • (Opens.restrictDifferentialOperators (I := I) U 1
          ⟨δ, δ.mem_differentialOperators_one⟩ : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) a := by
  ext x
  obtain ⟨g, hg⟩ := a.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
  obtain ⟨g', hg'⟩ := b.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
  have hprod : ((g * g' : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x]
      (a * b : C^∞⟮I, U; ℝ⟯) :=
    hg.mul hg'
  simp only [smul_eq_mul, ContMDiffMap.coe_add, ContMDiffMap.coe_mul, Pi.add_apply,
    Pi.mul_apply]
  rw [Opens.restrictDifferentialOperators_apply_of_eventuallyEq _ hprod,
    Opens.restrictDifferentialOperators_apply_of_eventuallyEq _ hg,
    Opens.restrictDifferentialOperators_apply_of_eventuallyEq _ hg', ← hg.eq_of_nhds,
    ← hg'.eq_of_nhds]
  simp [Derivation.leibniz]

variable (U) in
/-- **Restriction of a derivation to an open subset.** The restriction of a derivation `δ` of
`C^∞(M)`, a differential operator of order at most one, is a derivation of `C^∞(U)`: its value on
`f` at `x ∈ U` is `(δ g)(x)` for any `g ∈ C^∞(M)` agreeing with `f` near `x`. -/
def _root_.TopologicalSpace.Opens.restrictDerivation
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
    Derivation ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ :=
  Derivation.mk' (Opens.restrictDifferentialOperators (I := I) U 1
    ⟨δ, δ.mem_differentialOperators_one⟩ : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯)
    (restrictDifferentialOperators_leibniz δ)

/-- The restriction of `δ` sends the restriction of `g` to the restriction of `δ g`. -/
@[simp]
theorem _root_.TopologicalSpace.Opens.restrictDerivation_apply_restrict
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (g : C^∞⟮I, M; ℝ⟯) :
    U.restrictDerivation δ (g.restrict U) = (δ g).restrict U :=
  Opens.restrictDifferentialOperators_apply_restrict (I := I) (U := U) (m := 1)
    ⟨δ, δ.mem_differentialOperators_one⟩ g

/-- If the restriction of `g ∈ C^∞(M)` agrees with `f ∈ C^∞(U)` near `x`, then the restriction of
`δ` takes the value `(δ g)(x)` on `f` at `x`. -/
theorem _root_.TopologicalSpace.Opens.restrictDerivation_apply_of_eventuallyEq
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    {f : C^∞⟮I, U; ℝ⟯} {x : U} {g : C^∞⟮I, M; ℝ⟯} (hg : (g : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] f) :
    U.restrictDerivation δ f x = δ g x :=
  Opens.restrictDifferentialOperators_apply_of_eventuallyEq (I := I) (U := U) (m := 1)
    ⟨δ, δ.mem_differentialOperators_one⟩ hg

/-- As a differential operator of order at most one, the restriction of a derivation is the
restriction of the operator. -/
theorem _root_.TopologicalSpace.Opens.coe_restrictDerivation
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
    (U.restrictDerivation δ : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) =
      (Opens.restrictDifferentialOperators (I := I) U 1 ⟨δ, δ.mem_differentialOperators_one⟩ :
        C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) :=
  (rfl)

/-- **The vector field of a restricted derivation.** On a boundaryless manifold, the vector field
of the restriction of `δ` to `U` is the vector field of `δ` at the points of `U`, read in the
tangent spaces of `U`. -/
theorem _root_.Derivation.vectorField_restrictDerivation [BoundarylessManifold I M]
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (x : U) :
    (U.restrictDerivation δ).vectorField x =
      (Manifold.tangentSpaceOpenEquiv (I := I) x).symm (δ.vectorField (x : M)) := by
  refine (Derivation.eq_vectorField_iff.2 fun f ↦ ?_).symm
  obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
  have hd : mvfderiv I f x = mvfderiv I (g.restrict U) x := by
    rw [ContMDiffMap.coe_restrict]
    exact hg.symm.mvfderiv_eq
  rw [hd, mvfderiv_restrict, Opens.restrictDerivation_apply_of_eventuallyEq δ hg,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, Derivation.mvfderiv_vectorField]

end TauCeti
