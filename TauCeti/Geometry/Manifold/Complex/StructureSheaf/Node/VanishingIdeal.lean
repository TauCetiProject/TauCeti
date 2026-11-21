/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Node.Flat
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing

/-!
# The vanishing ideal of the smoothing family `xy = s(b)`

The local model for smoothing a node over a base `E` is the hypersurface
`N_s = {(b, x, y) | xy = s(b)}`, for a holomorphic base germ `s`. Its structure sheaf is the
quotient of the ambient holomorphic germs by the local equation `xy - s(b)`. This file shows that
this quotient is the ring of germs on `N_s` of ambient holomorphic functions: a holomorphic germ
vanishes on `N_s` near a point exactly when it is a multiple of `xy - s(b)`
(`TauCeti.holomorphicStructureSheaf.mem_span_smoothingEquation_iff`). Equivalently, the kernel of
restricting holomorphic germs to `N_s` is the ideal of the local equation
(`TauCeti.holomorphicStructureSheaf.ker_toFilterGerm_nhdsWithin_smoothingEquation`). No condition
is imposed on `s`: it may vanish identically (a permanent node) or to any order, as in `xy = b²`,
where the total space is singular. So the equation `xy - s(b)` alone defines `N_s` as a reduced
analytic subset, without an extra reducedness or admissibility assumption on the family.

Off the node, `N_s` is a graph over `E × ℂ` and this is Hadamard's lemma along the graph
(`mem_span_smoothingEquation_iff_of_fst_ne_zero`, `mem_span_smoothingEquation_iff_of_snd_ne_zero`).
At the node `((b, 0), 0)` (`TauCeti.holomorphicStructureSheaf.mem_span_nodeEquation_iff`), every
germ is congruent modulo `xy - s(b)` to `α(b, v) + β(b, v) u` in the coordinates `x = u + v`,
`y = u - v` (`bijective_nodeTransverseHom_add_mul`). Over a point `(b, v)` near `(b₀, 0)` both
square roots `u = ±t` of `v² + s(b)` give points of `N_s`, so vanishing on `N_s` forces
`α + β t = α - β t = 0`. Thus `α = 0` and `β² (v² + s(b)) = 0`, and `β = 0` because the germ
`v² + s(b)` is nonzero in the integral domain of holomorphic germs. This is the Rückert
Nullstellensatz for the radical ideal `(xy - s(b))` (`isRadical_span_nodeEquation`), proved
directly for this hypersurface.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for Weierstrass division and the vanishing ideals of analytic hypersurfaces.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the local models `xy = a` of nodal families.
-/

public section

open Filter Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The vanishing ideal at the node -/

/-- Over a point `(b, v)` near `(b₀, 0)`, both square roots `u` of `v² + S(b)` are small. If
`a(b, v) + c(b, v) u` vanishes at all such small roots, then `a = 0` and `c² (v² + S(b)) = 0` near
`(b₀, 0)`. -/
private theorem eventually_eq_zero_and_sq_mul_eq_zero {B : Type*} [TopologicalSpace B] {b₀ : B}
    {S : B → ℂ} (hS : ContinuousAt S b₀) (hS₀ : S b₀ = 0) {a c : B × ℂ → ℂ}
    (h : ∀ᶠ q : (B × ℂ) × ℂ in 𝓝 ((b₀, 0), 0),
      q.2 ^ 2 = q.1.2 ^ 2 + S q.1.1 → a q.1 + c q.1 * q.2 = 0) :
    ∀ᶠ w : B × ℂ in 𝓝 (b₀, 0), a w = 0 ∧ c w ^ 2 * (w.2 ^ 2 + S w.1) = 0 := by
  rw [nhds_prod_eq] at h
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.1 h
  obtain ⟨r, hr, hrQ⟩ := Metric.eventually_nhds_iff.1 hQ
  -- The discriminant `v² + S(b)` tends to `0` at `(b₀, 0)`, so eventually its roots lie in the
  -- ball of radius `r` on which `Q` holds.
  have hD : Tendsto (fun w : B × ℂ ↦ w.2 ^ 2 + S w.1) (𝓝 (b₀, 0)) (𝓝 0) := by
    have : ContinuousAt (fun w : B × ℂ ↦ w.2 ^ 2 + S w.1) (b₀, 0) :=
      (continuous_snd.continuousAt.pow 2).add (hS.comp continuousAt_fst)
    exact this.tendsto.mono_right (le_of_eq (by simp [hS₀]))
  filter_upwards [hP, hD.eventually (Metric.ball_mem_nhds 0 (pow_pos hr 2))] with w hw hDw
  set t := (w.2 ^ 2 + S w.1) ^ ((2 : ℕ)⁻¹ : ℂ)
  have ht : t ^ 2 = w.2 ^ 2 + S w.1 := Complex.cpow_nat_inv_pow _ two_ne_zero
  have htr : dist t 0 < r := by
    rw [dist_zero_right, ← ht, norm_pow] at hDw
    rw [dist_zero_right]
    exact lt_of_pow_lt_pow_left₀ 2 hr.le hDw
  have h₁ : a w + c w * t = 0 := hPQ hw (hrQ htr) ht
  have h₂ : a w + c w * -t = 0 :=
    hPQ hw (hrQ (by rwa [dist_zero_right, norm_neg, ← dist_zero_right])) (by rw [neg_sq, ht])
  refine ⟨by linear_combination (h₁ + h₂) / 2, ?_⟩
  rw [← ht]
  linear_combination (c w * t / 2) * (h₁ - h₂)

/-- If the class of `g` modulo `xy - s(b)` is `α(b, v) + β(b, v) u` in the coordinates
`x = u + v`, `y = u - v`, then on the hypersurface near the node a representative `G` of `g`
is `a(b, v) + c(b, v) u`, for representatives `a` of `α` and `c` of `β`. -/
private theorem eventually_eq_add_mul_of_nodeTransverseHom {b : E}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b} {S : E → ℂ}
    (hS : toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl s = S)
    {g : (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0)}
    {G : (E × ℂ) × ℂ → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0) (𝓝 ((b, 0), 0)) le_rfl g = G)
    {α β : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0)}
    {a c : E × ℂ → ℂ} (ha : AnalyticAt ℂ a (b, 0)) (hc : AnalyticAt ℂ c (b, 0))
    (haα : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (b, 0) (𝓝 (b, 0)) le_rfl α = a)
    (hcβ : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (b, 0) (𝓝 (b, 0)) le_rfl β = c)
    (h : nodeTransverseHom b s α + nodeTransverseHom b s β *
      Ideal.Quotient.mk _ (germOfContMDiff (fun z : (E × ℂ) × ℂ ↦ (z.1.2 + z.2) / 2)
        (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0)) = Ideal.Quotient.mk _ g) :
    ∀ᶠ z in 𝓝 ((b, (0 : ℂ)), (0 : ℂ)), z.1.2 * z.2 = S z.1.1 →
      G z = a (z.1.1, (z.1.2 - z.2) / 2) + c (z.1.1, (z.1.2 - z.2) / 2) * ((z.1.2 + z.2) / 2) := by
  have hτ (φ : E × ℂ → ℂ) (hφ : AnalyticAt ℂ φ (b, 0)) :
      AnalyticAt ℂ (fun z : (E × ℂ) × ℂ ↦ φ (z.1.1, (z.1.2 - z.2) / 2)) ((b, 0), 0) := by
    refine AnalyticAt.comp_of_eq hφ ?_ (by simp)
    exact (by fun_prop : ContDiff ℂ ω fun z : (E × ℂ) × ℂ ↦ (z.1.1, (z.1.2 - z.2) / 2))
      |>.contDiffAt.analyticAt
  obtain ⟨qa, hqa⟩ := exists_toFilterGerm_eq_of_analyticAt (hτ a ha)
  obtain ⟨qc, hqc⟩ := exists_toFilterGerm_eq_of_analyticAt (hτ c hc)
  rw [nodeTransverseHom_eq_mk haα (hqa _ le_rfl), nodeTransverseHom_eq_mk hcβ (hqc _ le_rfl),
    ← map_mul, ← map_add, Eq.comm, Ideal.Quotient.eq] at h
  -- Read `g - (qa + qc u) = k (xy - s(b))` on representatives.
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨K, -, hkK⟩ := exists_analyticAt_toFilterGerm_eq _ k
  have hK := congrArg (toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0)
    (𝓝 ((b, 0), 0)) le_rfl) hk
  simp only [map_mul, map_sub, map_add] at hK
  rw [hkK _ le_rfl, toFilterGerm_nodeEquation b 0 0 s hS, hgG, hqa _ le_rfl, hqc _ le_rfl,
    toFilterGerm_germOfContMDiff, ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_add, ← Germ.coe_sub,
    Germ.coe_eq] at hK
  filter_upwards [hK] with z hKz hzN
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply] at hKz
  rwa [hzN, sub_self, mul_zero, eq_comm, sub_eq_zero] at hKz

variable [FiniteDimensional ℂ E]

/-- At a node on the hypersurface, germs `α` and `β` at `(b, 0)` vanish if `α + β u` vanishes at
the points `((b, v), u)` with `u² = v² + s(b)` near `((b, 0), 0)`, for representatives `a` of `α`
and `c` of `β`. -/
private theorem eq_zero_and_eq_zero_of_eventually_add_mul_eq_zero {b : E}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b} {S : E → ℂ}
    (hS : toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl s = S) (hs : eval 𝓘(ℂ, E) E b s = 0)
    {α β : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (b, 0)}
    {a c : E × ℂ → ℂ} (haα : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (b, 0) (𝓝 (b, 0)) le_rfl α = a)
    (hcβ : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (b, 0) (𝓝 (b, 0)) le_rfl β = c)
    (h : ∀ᶠ q : (E × ℂ) × ℂ in 𝓝 ((b, 0), 0),
      q.2 ^ 2 = q.1.2 ^ 2 + S q.1.1 → a q.1 + c q.1 * q.2 = 0) :
    α = 0 ∧ β = 0 := by
  have hSc : ContinuousAt S b := (contMDiffAt_iff_contDiffAt.1
    (exists_toFilterGerm_nhds_eq_iff.1 ⟨s, hS⟩).self_of_nhds).continuousAt
  have hac := eventually_eq_zero_and_sq_mul_eq_zero hSc
    ((eval_eq_of_toFilterGerm_eq hS).symm.trans hs) h
  refine ⟨(eq_zero_iff_of_toFilterGerm_eq haα).2 (hac.mono fun _ h ↦ h.1), ?_⟩
  -- `β² (v² + s(b)) = 0` in the integral domain of germs, and the germ `v² + s(b)` is the
  -- vertical evaluation of the nonzero polynomial `X² + s`.
  have h0 : β ^ 2 * evalVertical b 0 (X ^ 2 + C s) = 0 := by
    refine (eq_zero_iff_of_toFilterGerm_eq
      (f := fun w : E × ℂ ↦ c w ^ 2 * ((w.2 - 0) ^ 2 + S w.1)) ?_).2
      (hac.mono fun _ h ↦ by simpa only [sub_zero, Pi.zero_apply] using h.2)
    simp only [map_mul, map_pow, map_add, evalVertical_X, evalVertical_C, hcβ,
      toFilterGerm_germOfContMDiff, toFilterGerm_stalkPrecomp, hS, Germ.coe_compTendsto]
    rfl
  exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h0).resolve_right
    ((map_ne_zero_iff _ (evalVertical_injective b 0)).2
      (monic_X_pow_add_C s two_ne_zero).ne_zero))

/-- **The vanishing ideal at a node.** At the node `((b, 0), 0)` of `xy = s(b)`, a holomorphic germ
lies in the ideal generated by `xy - s(b)` exactly when it vanishes on the hypersurface near the
node, for representatives `G` of the germ and `S` of `s`. This holds for every holomorphic base
germ `s`, including permanent nodes and singular total spaces such as `xy = b²`. If `s(b) ≠ 0`
both sides hold for every germ. -/
theorem mem_span_nodeEquation_iff {b : E}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b} {S : E → ℂ}
    (hS : toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl s = S)
    {g : (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, 0), 0)}
    {G : (E × ℂ) × ℂ → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, 0), 0) (𝓝 ((b, 0), 0)) le_rfl g = G) :
    g ∈ Ideal.span {nodeEquation b 0 0 s} ↔
      ∀ᶠ z in 𝓝 ((b, (0 : ℂ)), (0 : ℂ)), z.1.2 * z.2 = S z.1.1 → G z = 0 := by
  constructor
  · rw [Ideal.mem_span_singleton']
    rintro ⟨k, rfl⟩
    obtain ⟨K, -, hkK⟩ := exists_analyticAt_toFilterGerm_eq _ k
    rw [map_mul, hkK _ le_rfl, toFilterGerm_nodeEquation b 0 0 s hS, ← Germ.coe_mul,
      Germ.coe_eq] at hgG
    filter_upwards [hgG] with z hz hzN
    rw [← hz, Pi.mul_apply, hzN, sub_self, mul_zero]
  intro hG
  by_cases hs : eval 𝓘(ℂ, E) E b s = 0
  swap
  · -- Off the hypersurface the node equation is a unit.
    rw [Ideal.span_singleton_eq_top.2 ?_]
    · exact Submodule.mem_top
    rw [isUnit_stalk_iff, eval_nodeEquation, zero_mul, zero_sub, neg_ne_zero]
    exact hs
  -- Write `g ≡ α(b, v) + β(b, v) u` with `x = u + v`, `y = u - v`.
  obtain ⟨⟨α, β⟩, hαβ⟩ := (bijective_nodeTransverseHom_add_mul hs).2 (Ideal.Quotient.mk _ g)
  dsimp only at hαβ
  obtain ⟨a, ha, haα⟩ := exists_analyticAt_toFilterGerm_eq (b, (0 : ℂ)) α
  obtain ⟨c, hc, hcβ⟩ := exists_analyticAt_toFilterGerm_eq (b, (0 : ℂ)) β
  have hN := eventually_eq_add_mul_of_nodeTransverseHom hS hgG ha hc (haα _ le_rfl)
    (hcβ _ le_rfl) hαβ
  -- Pull back along `((b, v), u) ↦ ((b, u + v), u - v)`, which maps roots `u` of `v² + S(b)` to
  -- points of the hypersurface, where `a(b, v) + c(b, v) u = G = 0`.
  have hΨ : Tendsto (fun q : (E × ℂ) × ℂ ↦ ((q.1.1, q.2 + q.1.2), q.2 - q.1.2))
      (𝓝 ((b, 0), 0)) (𝓝 ((b, 0), 0)) := by
    have : Continuous fun q : (E × ℂ) × ℂ ↦ ((q.1.1, q.2 + q.1.2), q.2 - q.1.2) := by fun_prop
    simpa using this.tendsto ((b, 0), 0)
  have hroots : ∀ᶠ q : (E × ℂ) × ℂ in 𝓝 ((b, 0), 0),
      q.2 ^ 2 = q.1.2 ^ 2 + S q.1.1 → a q.1 + c q.1 * q.2 = 0 := by
    filter_upwards [hΨ.eventually hG, hΨ.eventually hN] with q hqG hqN hqr
    have hqr' : (q.2 + q.1.2) * (q.2 - q.1.2) = S q.1.1 := by linear_combination hqr
    have hv : (q.1.1, (q.2 + q.1.2 - (q.2 - q.1.2)) / 2) = q.1 := Prod.ext rfl (by ring)
    have hu : (q.2 + q.1.2 + (q.2 - q.1.2)) / 2 = q.2 := by ring
    simpa only [hv, hu, hqG hqr'] using (hqN hqr').symm
  obtain ⟨hα, hβ⟩ := eq_zero_and_eq_zero_of_eventually_add_mul_eq_zero hS hs (haα _ le_rfl)
    (hcβ _ le_rfl) hroots
  rw [hα, hβ, map_zero, zero_mul, add_zero, Eq.comm, Ideal.Quotient.eq_zero_iff_mem] at hαβ
  exact hαβ

/-! ### The vanishing ideal at every point -/

/-- The vanishing ideal at the node `(b, 0, 0)` in the coordinates of `OffNodeChart`, transported
from `mem_span_nodeEquation_iff` along the associator `((b, x), y) ↦ (b, x, y)`. -/
private theorem mem_span_smoothingEquation_node_iff {b : E}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b} {S : E → ℂ}
    (hS : toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl s = S)
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ)).presheaf.stalk (b, 0, 0)}
    {G : E × ℂ × ℂ → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) (b, 0, 0) (𝓝 (b, 0, 0)) le_rfl g = G) :
    g ∈ Ideal.span {smoothingEquation (b, 0, 0) s} ↔
      ∀ᶠ q in 𝓝 (b, (0 : ℂ), (0 : ℂ)), q.2.1 * q.2.2 = S q.1 → G q = 0 := by
  let e := RingEquiv.ofBijective _ (stalkPrecomp_assoc_bijective (E := E) ((b, 0), 0))
  have hmap : map (fun z : (E × ℂ) × ℂ ↦ (z.1.1, z.1.2, z.2)) (𝓝 ((b, 0), 0)) =
      𝓝 (b, (0 : ℂ), (0 : ℂ)) :=
    (Homeomorph.prodAssoc E ℂ ℂ).map_nhds_eq ((b, 0), 0)
  rw [Ideal.mem_span_singleton, ← map_dvd_iff e, ← Ideal.mem_span_singleton,
    RingEquiv.ofBijective_apply, stalkPrecomp_assoc_smoothingEquation,
    mem_span_nodeEquation_iff hS (by
      rw [RingEquiv.ofBijective_apply, toFilterGerm_stalkPrecomp, hgG, Germ.coe_compTendsto]),
    ← hmap, eventually_map]
  -- Both sides are the same statement about `(b, x, y) = ((b, x), y)`.
  rfl

/-- Near a point `p` of the hypersurface `xy = S(b)` with `x ≠ 0`, the hypersurface is the graph
`y = S(b)/x`, so vanishing on the graph is vanishing on the hypersurface. -/
private theorem eventually_graph_eq_zero_iff_of_fst_ne_zero {B : Type*} [TopologicalSpace B]
    {p : B × ℂ × ℂ} {S : B → ℂ}
    (hSc : ContinuousAt S p.1) (hSp : S p.1 = p.2.1 * p.2.2) (hx : p.2.1 ≠ 0)
    (G : B × ℂ × ℂ → ℂ) :
    (∀ᶠ w in 𝓝 (p.1, p.2.1), G (w.1, w.2, S w.1 / w.2) = 0) ↔
      ∀ᶠ q in 𝓝 p, q.2.1 * q.2.2 = S q.1 → G q = 0 := by
  have hσ : Tendsto (fun w : B × ℂ ↦ (w.1, w.2, S w.1 / w.2)) (𝓝 (p.1, p.2.1)) (𝓝 p) := by
    have hS₁ : ContinuousAt (fun w : B × ℂ ↦ S w.1) (p.1, p.2.1) :=
      hSc.comp_of_eq (f := (Prod.fst : B × ℂ → B)) continuousAt_fst rfl
    have : ContinuousAt (fun w : B × ℂ ↦ (w.1, w.2, S w.1 / w.2)) (p.1, p.2.1) :=
      continuousAt_fst.prodMk (continuousAt_snd.prodMk (hS₁.div continuousAt_snd hx))
    simpa [hSp, mul_div_cancel_left₀ _ hx] using this.tendsto
  have hπ : Tendsto (fun q : B × ℂ × ℂ ↦ (q.1, q.2.1)) (𝓝 p) (𝓝 (p.1, p.2.1)) :=
    (by fun_prop : Continuous fun q : B × ℂ × ℂ ↦ (q.1, q.2.1)).tendsto p
  constructor
  · intro h
    filter_upwards [hπ.eventually h, continuous_snd.fst.continuousAt.eventually_ne hx]
      with q hq hqx hqN
    rwa [← hqN, mul_div_cancel_left₀ _ hqx] at hq
  · intro h
    filter_upwards [hσ.eventually h, continuous_snd.continuousAt.eventually_ne hx] with w hw hwx
    exact hw (mul_div_cancel₀ _ hwx)

/-- Near a point `p` of the hypersurface `xy = S(b)` with `y ≠ 0`, the hypersurface is the graph
`x = S(b)/y`, so vanishing on the graph is vanishing on the hypersurface. -/
private theorem eventually_graph_eq_zero_iff_of_snd_ne_zero {B : Type*} [TopologicalSpace B]
    {p : B × ℂ × ℂ} {S : B → ℂ}
    (hSc : ContinuousAt S p.1) (hSp : S p.1 = p.2.1 * p.2.2) (hy : p.2.2 ≠ 0)
    (G : B × ℂ × ℂ → ℂ) :
    (∀ᶠ w in 𝓝 (p.1, p.2.2), G (w.1, S w.1 / w.2, w.2) = 0) ↔
      ∀ᶠ q in 𝓝 p, q.2.1 * q.2.2 = S q.1 → G q = 0 := by
  have hσ : Tendsto (fun w : B × ℂ ↦ (w.1, S w.1 / w.2, w.2)) (𝓝 (p.1, p.2.2)) (𝓝 p) := by
    have hS₁ : ContinuousAt (fun w : B × ℂ ↦ S w.1) (p.1, p.2.2) :=
      hSc.comp_of_eq (f := (Prod.fst : B × ℂ → B)) continuousAt_fst rfl
    have : ContinuousAt (fun w : B × ℂ ↦ (w.1, S w.1 / w.2, w.2)) (p.1, p.2.2) :=
      continuousAt_fst.prodMk ((hS₁.div continuousAt_snd hy).prodMk continuousAt_snd)
    simpa [hSp, mul_div_cancel_right₀ _ hy] using this.tendsto
  have hπ : Tendsto (fun q : B × ℂ × ℂ ↦ (q.1, q.2.2)) (𝓝 p) (𝓝 (p.1, p.2.2)) :=
    (by fun_prop : Continuous fun q : B × ℂ × ℂ ↦ (q.1, q.2.2)).tendsto p
  constructor
  · intro h
    filter_upwards [hπ.eventually h, continuous_snd.snd.continuousAt.eventually_ne hy]
      with q hq hqy hqN
    rwa [← hqN, mul_div_cancel_right₀ _ hqy] at hq
  · intro h
    filter_upwards [hσ.eventually h, continuous_snd.continuousAt.eventually_ne hy] with w hw hwy
    exact hw (div_mul_cancel₀ _ hwy)

/-- **The vanishing ideal of `N_s`.** At every point `p = (b, x, y)` of `E × ℂ × ℂ`, a holomorphic
germ lies in the ideal generated by the local equation `xy - s(b)` exactly when it vanishes on the
hypersurface `xy = s(b)` near `p`, for representatives `G` of the germ and `S` of `s`. No condition
is imposed on `s`: permanent nodes and singular total spaces are included. -/
theorem mem_span_smoothingEquation_iff {p : E × ℂ × ℂ}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk p.1} {S : E → ℂ}
    (hS : toFilterGerm 𝓘(ℂ, E) E p.1 (𝓝 p.1) le_rfl s = S)
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ)).presheaf.stalk p}
    {G : E × ℂ × ℂ → ℂ} (hgG : toFilterGerm 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) p (𝓝 p) le_rfl g = G) :
    g ∈ Ideal.span {smoothingEquation p s} ↔ ∀ᶠ q in 𝓝 p, q.2.1 * q.2.2 = S q.1 → G q = 0 := by
  have hSc : ContinuousAt S p.1 := (contMDiffAt_iff_contDiffAt.1
    (exists_toFilterGerm_nhds_eq_iff.1 ⟨s, hS⟩).self_of_nhds).continuousAt
  have hSp : eval 𝓘(ℂ, E) E p.1 s = S p.1 := eval_eq_of_toFilterGerm_eq hS
  by_cases hs : eval 𝓘(ℂ, E) E p.1 s = p.2.1 * p.2.2
  swap
  · -- Off `N_s` the local equation is a unit, and the points near `p` are off `N_s`.
    have hu : IsUnit (smoothingEquation p s) := by
      rw [isUnit_stalk_iff, eval_smoothingEquation, sub_ne_zero]
      exact Ne.symm hs
    rw [Ideal.span_singleton_eq_top.2 hu]
    refine iff_of_true Submodule.mem_top ?_
    have hc : ContinuousAt (fun q : E × ℂ × ℂ ↦ q.2.1 * q.2.2 - S q.1) p :=
      (continuous_snd.fst.mul continuous_snd.snd).continuousAt.sub (hSc.comp continuousAt_fst)
    filter_upwards [hc.eventually_ne (by rwa [sub_ne_zero, ← hSp, ne_comm])] with q hq hqN
    exact absurd (sub_eq_zero.2 hqN) hq
  by_cases hx : p.2.1 = 0
  · by_cases hy : p.2.2 = 0
    · obtain ⟨b, x, y⟩ := p
      dsimp only at hx hy
      subst hx hy
      exact mem_span_smoothingEquation_node_iff hS hgG
    rw [mem_span_smoothingEquation_iff_of_snd_ne_zero hy hs hS g G hgG,
      eventually_graph_eq_zero_iff_of_snd_ne_zero hSc (hSp.symm.trans hs) hy]
  rw [mem_span_smoothingEquation_iff_of_fst_ne_zero hx hs hS g G hgG,
    eventually_graph_eq_zero_iff_of_fst_ne_zero hSc (hSp.symm.trans hs) hx]

/-- **The structure sheaf of `N_s` consists of restricted holomorphic functions.** At every point
`p` of `E × ℂ × ℂ`, the kernel of restricting holomorphic germs at `p` to germs on the hypersurface
`xy = S(b)` is the ideal generated by the local equation `xy - s(b)`, for any representative `S` of
`s`. Thus the local ring `𝒪_p ⧸ (xy - s(b))` of `N_s` embeds into the germs of functions on `N_s`
at `p`, with image the restrictions of ambient holomorphic germs. -/
theorem ker_toFilterGerm_nhdsWithin_smoothingEquation {p : E × ℂ × ℂ}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk p.1} {S : E → ℂ}
    (hS : toFilterGerm 𝓘(ℂ, E) E p.1 (𝓝 p.1) le_rfl s = S) :
    RingHom.ker (toFilterGerm 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) p
      (𝓝[{q | q.2.1 * q.2.2 = S q.1}] p) nhdsWithin_le_nhds) =
      Ideal.span {smoothingEquation p s} := by
  ext g
  obtain ⟨G, -, hG⟩ := exists_toFilterGerm_eq p g
  rw [RingHom.mem_ker, hG, mem_span_smoothingEquation_iff hS (hG _ le_rfl), ← Germ.coe_zero,
    Germ.coe_eq, EventuallyEq, eventually_nhdsWithin_iff]
  rfl

end TauCeti.holomorphicStructureSheaf
