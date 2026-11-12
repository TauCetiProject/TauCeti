/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformApproximation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.ContinuousSMul
public import TauCeti.Topology.Compactification.OnePoint.Stabilizer

/-!
# Reparametrizing maps of the Riemann sphere by Möbius transformations

The group `PSL(2, 𝕜)` of Möbius transformations acts on maps `u` out of the projective line
`OnePoint 𝕜` by precomposition, `(u, g) ↦ u ∘ (g • ·)`. For `𝕜 = ℂ` this is the action of the
automorphism group of the Riemann sphere on parametrized spheres, whose quotient is the space of
unparametrized spheres. This file proves the two properties of this action that make such a
quotient well behaved: it is free on maps with an injective point, and proper on nonconstant maps.

## Escaping sequences of Möbius transformations

The properness rests on the way a sequence of Möbius transformations can leave every compact
subset of `PSL(2, 𝕜)`. Lift `g n` to matrices `A n` of determinant one. They are unbounded, and
after dividing each by its entry of largest norm a subsequence converges to a nonzero matrix `B`
whose determinant is the limit of `(A n i j)⁻²`, hence zero
(`Matrix.ProjectiveSpecialLinearGroup.exists_tendsto_inv_smul_of_tendsto_cocompact`). So `B` has
rank one, with a kernel line `a` and an image line `b` (`Matrix.exists_ker_range_of_det_eq_zero`),
and `g n • z` converges to `b` for every `z ≠ a`, by the limit theorem
`Projectivization.tendsto_smul_of_tendsto_smul_coe`. This holds even along moving points:
if `z n → z₀ ≠ a` then `g n • z n → b` along the subsequence
(`OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact`), so that the transformations converge
to the constant map `b` away from the point `a`. For instance the dilations `z ↦ n z` converge to
`∞` away from `0`.

## Properness and freeness of the reparametrization action

Let `u n → u₀` and `u n ∘ (g n • ·) → v₀` uniformly, with `u₀` and `v₀` continuous and `v₀`
nonconstant. If the `g n` escaped to infinity, the maps `u n ∘ (g n • ·)` would converge to the
constant `u₀ b` away from `a`, so `v₀` would be constant. Hence a subsequence of `g n` converges,
to some `g₀` with `v₀ = u₀ ∘ (g₀ • ·)` (`OnePoint.exists_tendsto_psl_of_tendstoUniformly`). This is
the properness of `(u, g) ↦ (u, u ∘ (g • ·))` on nonconstant maps, in the sequential form, for
`C⁰` convergence; convergence in finer topologies, such as the `C^∞` topology on smooth maps,
implies it.

A point `z` is an *injective point* of `u` when `u` is injective near `z` and no other point has
the same image. For a `C¹` map with injective derivative at `z`, such as a pseudoholomorphic map
with nonvanishing derivative, the first condition holds automatically
(`ContMDiffAt.exists_mem_nhds_injOn`). If `u ∘ (g • ·) = u` and `z` is an injective point, then
`g` fixes `z`, hence fixes every point near `z`, hence fixes three distinct points, so `g = 1`
(`OnePoint.eq_one_of_forall_apply_smul_eq`). So the action is free on maps with an injective point
(`OnePoint.eq_of_forall_apply_smul_eq_apply_smul`). For pseudoholomorphic spheres, having an
injective point is equivalent to being simple, that is, not multiply covered; that equivalence is
not proved here.

## Main results

* `OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact`: a sequence of Möbius transformations
  escaping to infinity has a subsequence converging to a constant `b` away from a point `a`, even
  along moving points.
* `OnePoint.exists_tendsto_psl_of_tendstoUniformly`: properness of the reparametrization action
  on nonconstant maps.
* `OnePoint.eq_one_of_forall_apply_smul_eq`: a Möbius transformation preserving a map with an
  injective point is the identity.
* `OnePoint.eq_of_forall_apply_smul_eq_apply_smul`: freeness of the reparametrization action on
  maps with an injective point.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012 (the reparametrization action on simple
  spheres).
* A. Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer, 1983
  (sequences of Möbius transformations).
-/

public section

open Filter Function Topology Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-! ### Escaping sequences -/

/-- **Escaping sequences of Möbius transformations.** If a sequence `g n` of Möbius
transformations leaves every compact subset of `PSL(2, 𝕜)`, a subsequence converges to a constant
`b` away from a point `a`, even along moving points: whenever `z n → z₀ ≠ a`, the points
`g (φ n) • z n` converge to `b`. -/
theorem exists_tendsto_psl_smul_of_tendsto_cocompact {g : ℕ → PSL(2, 𝕜)}
    (hg : Tendsto g atTop (cocompact PSL(2, 𝕜))) :
    ∃ (φ : ℕ → ℕ) (a b : OnePoint 𝕜), StrictMono φ ∧
      ∀ ⦃z : ℕ → OnePoint 𝕜⦄ ⦃z₀ : OnePoint 𝕜⦄, z₀ ≠ a → Tendsto z atTop (𝓝 z₀) →
        Tendsto (fun n ↦ g (φ n) • z n) atTop (𝓝 b) := by
  choose A hA using fun n ↦ QuotientGroup.mk_surjective (g n)
  obtain ⟨m, φ, B, hφ, hB, hdet, hCB⟩ :=
    Matrix.ProjectiveSpecialLinearGroup.exists_tendsto_inv_smul_of_tendsto_cocompact hg hA
  obtain ⟨a, b, ha, hb⟩ := Matrix.exists_ker_range_of_det_eq_zero hB hdet
  let e := (diffeomorphProjectivization 𝕜 0).toHomeomorph
  refine ⟨φ, e.symm a, e.symm b, hφ, fun z z₀ hz₀ hz ↦ ?_⟩
  -- On the projective line the transformations act through the matrices `A n`, and
  -- `(m n)⁻¹ • A n → B`, so `Projectivization.tendsto_smul_of_tendsto_smul_coe` applies.
  have hBz : B *ᵥ (e z₀).rep ≠ 0 := fun h ↦ hz₀ <| by
    rw [← ha _ (e z₀).rep_ne_zero h, Projectivization.mk_rep, Homeomorph.symm_apply_apply]
  have hlim := Projectivization.tendsto_smul_of_tendsto_smul_coe
    (C := fun n ↦ (A (φ n) : GL (Fin 2) 𝕜)) (c := fun n ↦ (m (φ n))⁻¹) hCB
    ((e.continuous.tendsto z₀).comp hz) hBz
  rw [hb] at hlim
  refine ((e.symm.continuous.tendsto b).comp hlim).congr fun n ↦ ?_
  simp only [Function.comp_apply, ← hA (φ n)]
  exact e.injective (by simpa [e] using (equivProjectivization_smul (z n)).symm)

/-! ### Properness and freeness of the reparametrization action -/

/-- **Properness of the reparametrization action on nonconstant maps.** Let maps `u n` of the
projective line converge uniformly to a continuous map `u₀`, and their reparametrizations
`u n ∘ (g n • ·)` by Möbius transformations converge uniformly to a continuous nonconstant map
`v₀`. Then a subsequence of `g n` converges, to a Möbius transformation `g₀` with
`v₀ = u₀ ∘ (g₀ • ·)`. -/
theorem exists_tendsto_psl_of_tendstoUniformly {X : Type*} [UniformSpace X] [T2Space X]
    {u : ℕ → OnePoint 𝕜 → X} {u₀ v₀ : OnePoint 𝕜 → X} {g : ℕ → PSL(2, 𝕜)}
    (hu : TendstoUniformly u u₀ atTop) (hu₀ : Continuous u₀)
    (hv : TendstoUniformly (fun n z ↦ u n (g n • z)) v₀ atTop) (hv₀ : Continuous v₀)
    (hconst : ∃ z w, v₀ z ≠ v₀ w) :
    ∃ (φ : ℕ → ℕ) (g₀ : PSL(2, 𝕜)), StrictMono φ ∧ Tendsto (g ∘ φ) atTop (𝓝 g₀) ∧
      ∀ z, v₀ z = u₀ (g₀ • z) := by
  -- Along a subsequence `φ`, if `g (φ n) • z → y` then `v₀ z = u₀ y`.
  have hlim : ∀ {φ : ℕ → ℕ}, StrictMono φ → ∀ {z y : OnePoint 𝕜},
      Tendsto (fun n ↦ g (φ n) • z) atTop (𝓝 y) → v₀ z = u₀ y := fun {φ} hφ {z y} hzy ↦
    tendsto_nhds_unique ((hv.tendsto_at z).comp hφ.tendsto_atTop)
      (TendstoUniformly.tendsto_comp (fun U hU ↦ hφ.tendsto_atTop.eventually (hu U hU))
        hu₀.continuousAt hzy)
  by_cases hesc : Tendsto g atTop (cocompact PSL(2, 𝕜))
  · -- If `g` escaped, `v₀` would be the constant `u₀ b` off the point `a`, hence constant.
    obtain ⟨φ, a, b, hφ, hab⟩ := exists_tendsto_psl_smul_of_tendsto_cocompact hesc
    have hv₀b : v₀ = fun _ ↦ u₀ b :=
      hv₀.ext_on (dense_compl_singleton a) continuous_const fun z hz ↦
        hlim hφ (hab hz tendsto_const_nhds)
    obtain ⟨z, w, hzw⟩ := hconst
    exact (hzw (by simp [hv₀b])).elim
  · -- Otherwise `g` returns infinitely often to a compact set, where a subsequence converges.
    obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hesc
    obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 hs
    obtain ⟨ψ, hψ, hψK⟩ := extraction_of_frequently_atTop (P := fun n ↦ g n ∈ K)
      (hfreq.mono fun n hn ↦ by_contra fun h ↦ hn (hKs h))
    obtain ⟨g₀, -, φ, hφ, hconv⟩ := hK.tendsto_subseq (x := g ∘ ψ) hψK
    exact ⟨ψ ∘ φ, g₀, hψ.comp hφ, hconv, fun z ↦ hlim (hψ.comp hφ) (hconv.smul_const z)⟩

/-- **A Möbius transformation preserving a map with an injective point is the identity.** Let `u`
be injective on a neighbourhood `t` of `z`, with no other point having the image `u z`. If
`u (g • w) = u w` for every `w`, then `g = 1`. -/
theorem eq_one_of_forall_apply_smul_eq {X : Type*} {u : OnePoint 𝕜 → X} {z : OnePoint 𝕜}
    {t : Set (OnePoint 𝕜)} (ht : t ∈ 𝓝 z) (hinj : Set.InjOn u t) (hfib : ∀ w, u w = u z → w = z)
    {g : PSL(2, 𝕜)} (hg : ∀ w, u (g • w) = u w) : g = 1 := by
  -- `g` fixes `z`, hence every point of the neighbourhood `s` of `z`.
  have hgz : g • z = z := hfib _ (hg z)
  have hs : t ∩ (g • ·) ⁻¹' t ∈ 𝓝 z :=
    inter_mem ht ((continuous_const_smul g).continuousAt.preimage_mem_nhds (by rwa [hgz]))
  have hfix : ∀ w ∈ t ∩ (g • ·) ⁻¹' t, g • w = w := fun w hw ↦ hinj hw.2 hw.1 (hg w)
  -- The neighbourhood contains three distinct points, and only `1` fixes three distinct points.
  have hinf := infinite_of_mem_nhds z hs
  obtain ⟨x, hx⟩ := hinf.nonempty
  obtain ⟨y, hy, hyx⟩ := (hinf.sdiff (Set.finite_singleton x)).nonempty
  obtain ⟨w, hw, hwxy⟩ := (hinf.sdiff (Set.toFinite {x, y})).nonempty
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, not_or] at hyx hwxy
  have hmem : g ∈ fixingSubgroup PSL(2, 𝕜) {x, y, w} := by
    rw [mem_fixingSubgroup_iff]
    rintro p (rfl | rfl | rfl)
    exacts [hfix _ hx, hfix _ hy, hfix _ hw]
  rwa [fixingSubgroup_psl_eq_bot (Ne.symm hyx) (Ne.symm hwxy.1) (Ne.symm hwxy.2),
    Subgroup.mem_bot] at hmem

/-- **The reparametrization action is free on maps with an injective point.** If `u` has an
injective point `z` and `u ∘ (g • ·) = u ∘ (h • ·)`, then `g = h`. -/
theorem eq_of_forall_apply_smul_eq_apply_smul {X : Type*} {u : OnePoint 𝕜 → X} {z : OnePoint 𝕜}
    {t : Set (OnePoint 𝕜)} (ht : t ∈ 𝓝 z) (hinj : Set.InjOn u t) (hfib : ∀ w, u w = u z → w = z)
    {g h : PSL(2, 𝕜)} (hgh : ∀ w, u (g • w) = u (h • w)) : g = h := by
  have := eq_one_of_forall_apply_smul_eq ht hinj hfib (g := g * h⁻¹) fun w ↦ by
    simpa [mul_smul] using hgh (h⁻¹ • w)
  rwa [mul_inv_eq_one] at this

end OnePoint
