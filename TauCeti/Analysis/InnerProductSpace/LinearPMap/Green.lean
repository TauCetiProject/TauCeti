/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Eigenbasis
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralCutoff

/-!
# The Green operator of a self-adjoint operator with compact resolvent

Let `A` be a self-adjoint partial linear map with compact resolvent on a complex Hilbert space
`H`, such as a self-adjoint elliptic operator on a closed manifold, or the Laplacian of an
elliptic complex. Its kernel `ker A` is finite-dimensional, and `A` is bounded below on
`D(A) ∩ (ker A)ᗮ`: there is `c > 0`, the least absolute value of a nonzero eigenvalue when there
is one, with `c ‖u‖ ≤ ‖A u‖` there. Consequently the range of `A` is closed and equals
`(ker A)ᗮ`, so that `A u = f` is solvable exactly when `f` is orthogonal to `ker A`, and
`H = ker A ⊕ range A` is an orthogonal splitting, the abstract Hodge decomposition.

The **Green operator** `G = A.greenOperator hA h` is the bounded operator that vanishes on
`ker A` and inverts `A` on `(ker A)ᗮ`. With `Π` the orthogonal projection onto `ker A`, it
satisfies

`A G f = f - Π f`, `G A u = u - Π u`,

for `f ∈ H` and `u ∈ D(A)`. It is self-adjoint and compact, its range is `D(A) ∩ (ker A)ᗮ`, its
norm is at most `c⁻¹`, and it acts on an eigenvector of `A` with nonzero eigenvalue `μ` as
multiplication by `μ⁻¹`. If `ker A = H` then `G = 0`.

## Main results

* `IsSelfAdjoint.exists_pos_mul_norm_le_norm_apply_of_mem_orthogonal_ker`: with compact
  resolvent, `A` is bounded below on `D(A) ∩ (ker A)ᗮ`.
* `IsSelfAdjoint.range_eq_orthogonal_ker`, `IsSelfAdjoint.exists_apply_eq_iff_mem_orthogonal_ker`
  and `IsSelfAdjoint.isCompl_ker_range`: the range is closed and equal to `(ker A)ᗮ`, the
  solvability criterion, and the orthogonal splitting `H = ker A ⊕ range A`.
* `LinearPMap.greenOperator`: the Green operator, with `LinearPMap.apply_greenOperator`,
  `LinearPMap.greenOperator_apply_apply`, `LinearPMap.isSelfAdjoint_greenOperator`,
  `LinearPMap.isCompactOperator_greenOperator` and `LinearPMap.norm_greenOperator_le`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Springer GTM 94,
  §§6.8–6.10.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- **Spectral gap on the kernel complement.** A self-adjoint operator with compact resolvent is
bounded below on `D(A) ∩ (ker A)ᗮ`: there is `c > 0` with `c ‖u‖ ≤ ‖A u‖` there. When `A` has a
nonzero eigenvalue, `c` can be taken to be the least absolute value of one. -/
theorem _root_.IsSelfAdjoint.exists_pos_mul_norm_le_norm_apply_of_mem_orthogonal_ker
    (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    ∃ c > 0, ∀ u : A.domain, (u : H) ∈ A.kerᗮ → c * ‖(u : H)‖ ≤ ‖A u‖ := by
  obtain ⟨κ, b, lam, hb⟩ := hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h
  obtain ⟨c, hc, hgap⟩ := h.exists_pos_mul_norm_le_norm_apply b hA.isFormalAdjoint hb
  refine ⟨c, hc, fun u hu ↦ hgap u fun k hk ↦ ?_⟩
  obtain ⟨hk', hbk⟩ := hb k
  refine Submodule.inner_right_of_mem_orthogonal (mem_ker_iff.2 ⟨⟨b k, hk'⟩, rfl, ?_⟩) hu
  rw [hbk, hk, Complex.ofReal_zero, zero_smul]

/-- **Closed range.** A self-adjoint operator with compact resolvent has closed range. -/
theorem _root_.IsSelfAdjoint.isClosed_range (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    _root_.IsClosed (LinearMap.range A.toFun : Set H) := by
  have := h.hasOrthogonalProjection_ker
  obtain ⟨c, hc, hbound⟩ := hA.exists_pos_mul_norm_le_norm_apply_of_mem_orthogonal_ker h
  refine isClosed_of_closure_subset fun f hf ↦ ?_
  obtain ⟨g, hg, hgf⟩ := mem_closure_iff_seq_limit.1 hf
  -- Choose preimages `v n` of `g n` orthogonal to the kernel.
  have hpre : ∀ n, ∃ v : A.domain, (v : H) ∈ A.kerᗮ ∧ A v = g n := fun n ↦ by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (hg n)
    obtain ⟨v, hv, hAv⟩ := exists_coe_eq_sub_starProjection u
    exact ⟨v, hv ▸ A.ker.sub_starProjection_mem_orthogonal (u : H), hAv.trans hu⟩
  choose v hv hAv using hpre
  -- By the lower bound, `v` is a Cauchy sequence, since `g` is.
  have hcauchy : CauchySeq fun n ↦ (v n : H) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hgf.cauchySeq (c * ε) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hmn := hbound (v m - v n) (sub_mem (hv m) (hv n))
    rw [map_sub, hAv, hAv, Submodule.coe_sub, ← dist_eq_norm, ← dist_eq_norm] at hmn
    exact lt_of_mul_lt_mul_left (hmn.trans_lt (hN m hm n hn)) hc.le
  -- Its limit `w` satisfies `A w = f`, since `A` is closed.
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hcl : _root_.IsClosed (A.graph : Set (H × H)) := hA.isClosed
  have hmem : (w, f) ∈ A.graph := hcl.mem_of_tendsto (hw.prodMk_nhds hgf)
    (Filter.Eventually.of_forall fun n ↦ by rw [← hAv n]; exact A.mem_graph (v n))
  obtain ⟨y, -, hy⟩ := (mem_graph_iff A).1 hmem
  exact ⟨y, hy⟩

/-- **Fredholm alternative.** The range of a self-adjoint operator with compact resolvent is the
orthogonal complement of its kernel. -/
theorem _root_.IsSelfAdjoint.range_eq_orthogonal_ker (hA : IsSelfAdjoint A)
    (h : A.HasCompactResolvent) : LinearMap.range A.toFun = A.kerᗮ := by
  rw [← hA.orthogonal_range_eq_ker, Submodule.orthogonal_orthogonal_eq_closure,
    (hA.isClosed_range h).submodule_topologicalClosure_eq]

/-- **Solvability.** For a self-adjoint operator with compact resolvent, `A u = f` has a solution
`u ∈ D(A)` exactly when `f` is orthogonal to the kernel of `A`. -/
theorem _root_.IsSelfAdjoint.exists_apply_eq_iff_mem_orthogonal_ker (hA : IsSelfAdjoint A)
    (h : A.HasCompactResolvent) {f : H} : (∃ u : A.domain, A u = f) ↔ f ∈ A.kerᗮ := by
  rw [← hA.range_eq_orthogonal_ker h, LinearMap.mem_range]
  rfl

/-- **Hodge splitting.** For a self-adjoint operator with compact resolvent, `H` is the orthogonal
direct sum of the kernel and the range. -/
theorem _root_.IsSelfAdjoint.isCompl_ker_range (hA : IsSelfAdjoint A)
    (h : A.HasCompactResolvent) : IsCompl A.ker (LinearMap.range A.toFun) := by
  have := h.hasOrthogonalProjection_ker
  rw [hA.range_eq_orthogonal_ker h]
  exact A.ker.isCompl_orthogonal

/-! ### The Green operator -/

/-- The restriction of `A` to `D(A) ∩ (ker A)ᗮ`, with values in `(ker A)ᗮ`. -/
private def kerOrthogonalPart (A : H →ₗ.[ℂ] H) (hA : A.IsFormalAdjoint A) :
    A.kerᗮ.comap A.domain.subtype →ₗ[ℂ] A.kerᗮ :=
  LinearMap.codRestrict A.kerᗮ (A.toFun ∘ₗ (A.kerᗮ.comap A.domain.subtype).subtype) fun x ↦
    hA.range_le_orthogonal_ker (LinearMap.mem_range_self A.toFun x)

omit [CompleteSpace H] in
private theorem coe_kerOrthogonalPart (hA : A.IsFormalAdjoint A)
    (x : A.kerᗮ.comap A.domain.subtype) : (kerOrthogonalPart A hA x : H) = A x :=
  rfl

private theorem bijective_kerOrthogonalPart (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    Function.Bijective (kerOrthogonalPart A hA.isFormalAdjoint) := by
  have := h.hasOrthogonalProjection_ker
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun f ↦ ?_⟩
  · -- An element of the kernel orthogonal to the kernel vanishes.
    have hx' : ((x : A.domain) : H) ∈ A.ker ⊓ A.kerᗮ :=
      ⟨coe_mem_ker_iff.2 (by
        rw [← coe_kerOrthogonalPart hA.isFormalAdjoint, hx, ZeroMemClass.coe_zero]), x.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hx'
    exact Subtype.ext (Subtype.ext hx')
  · obtain ⟨u, hu⟩ := (hA.exists_apply_eq_iff_mem_orthogonal_ker h).2 f.2
    obtain ⟨v, hv, hAv⟩ := exists_coe_eq_sub_starProjection u
    refine ⟨⟨v, ?_⟩, Subtype.ext ?_⟩
    · rw [Submodule.mem_comap, Submodule.subtype_apply, hv]
      exact A.ker.sub_starProjection_mem_orthogonal _
    · rw [coe_kerOrthogonalPart, hAv, hu]

/-- The Green operator as a linear map: invert `kerOrthogonalPart` after projecting onto
`(ker A)ᗮ`. -/
private def greenLinearMap (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    H →ₗ[ℂ] H :=
  haveI := h.hasOrthogonalProjection_ker
  A.domain.subtype ∘ₗ (A.kerᗮ.comap A.domain.subtype).subtype ∘ₗ
    (LinearEquiv.ofBijective _ (bijective_kerOrthogonalPart hA h)).symm.toLinearMap ∘ₗ
      (A.kerᗮ.orthogonalProjectionOnto : H →ₗ[ℂ] A.kerᗮ)

/-- The characteristic properties of `greenLinearMap`: its values lie in `D(A) ∩ (ker A)ᗮ` and
`A` maps them back to `f - Π f`. -/
private theorem greenLinearMap_spec [A.ker.HasOrthogonalProjection] (hA : IsSelfAdjoint A)
    (h : A.HasCompactResolvent) (f : H) :
    ∃ u : A.domain, (u : H) = greenLinearMap A hA h f ∧ (u : H) ∈ A.kerᗮ ∧
      A u = f - A.ker.starProjection f := by
  set e := LinearEquiv.ofBijective _ (bijective_kerOrthogonalPart hA h)
  set w := e.symm (A.kerᗮ.orthogonalProjectionOnto f)
  have hw : kerOrthogonalPart A hA.isFormalAdjoint w = A.kerᗮ.orthogonalProjectionOnto f :=
    e.apply_symm_apply _
  refine ⟨w, rfl, w.2, ?_⟩
  rw [← coe_kerOrthogonalPart hA.isFormalAdjoint, hw, ← Submodule.starProjection_apply,
    Submodule.starProjection_orthogonal_val]

/-- The Green operator is bounded by `c⁻¹` whenever `A` is bounded below by `c` on the kernel
complement. -/
private theorem norm_greenLinearMap_le (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ u : A.domain, (u : H) ∈ A.kerᗮ → c * ‖(u : H)‖ ≤ ‖A u‖) (f : H) :
    ‖greenLinearMap A hA h f‖ ≤ c⁻¹ * ‖f‖ := by
  have := h.hasOrthogonalProjection_ker
  obtain ⟨u, hu, huK, hAu⟩ := greenLinearMap_spec hA h f
  rw [← hu, le_inv_mul_iff₀ hc]
  refine (hbound u huK).trans ?_
  rw [hAu, ← Submodule.starProjection_orthogonal_val]
  exact A.kerᗮ.norm_starProjection_apply_le f

/-- The **Green operator** of a self-adjoint operator `A` with compact resolvent on a complex
Hilbert space: the bounded operator vanishing on `ker A` and inverting `A` on `(ker A)ᗮ`. For
`f ∈ H`, `G f` is the unique `u ∈ D(A) ∩ (ker A)ᗮ` with `A u = f - Π f`, where `Π` is the
orthogonal projection onto `ker A` (`LinearPMap.apply_greenOperator`,
`LinearPMap.greenOperator_eq_of_apply_eq`). -/
def greenOperator (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    H →L[ℂ] H :=
  (greenLinearMap A hA h).mkContinuousOfExistsBound <| by
    obtain ⟨c, hc, hbound⟩ := hA.exists_pos_mul_norm_le_norm_apply_of_mem_orthogonal_ker h
    exact ⟨c⁻¹, norm_greenLinearMap_le hA h hc hbound⟩

variable (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

/-- The Green operator takes values in the domain of `A`. -/
theorem greenOperator_mem_domain (f : H) : A.greenOperator hA h f ∈ A.domain := by
  have := h.hasOrthogonalProjection_ker
  obtain ⟨u, hu, -, -⟩ := greenLinearMap_spec hA h f
  exact hu ▸ u.2

/-- The Green operator takes values in the orthogonal complement of the kernel of `A`. -/
theorem greenOperator_mem_orthogonal_ker (f : H) : A.greenOperator hA h f ∈ A.kerᗮ := by
  have := h.hasOrthogonalProjection_ker
  obtain ⟨u, hu, huK, -⟩ := greenLinearMap_spec hA h f
  exact hu ▸ huK

/-- **`A G = 1 - Π`**: the Green operator inverts `A` up to the projection `Π` onto its kernel. -/
@[simp]
theorem apply_greenOperator [A.ker.HasOrthogonalProjection] (f : H) :
    A ⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩ = f - A.ker.starProjection f := by
  obtain ⟨u, hu, -, hAu⟩ := greenLinearMap_spec hA h f
  have hu' : u = ⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩ := Subtype.ext hu
  rw [← hu', hAu]

/-- **Uniqueness.** `G f` is the only `u ∈ D(A) ∩ (ker A)ᗮ` with `A u = f - Π f`. -/
theorem greenOperator_eq_of_apply_eq [A.ker.HasOrthogonalProjection] {f : H} {u : A.domain}
    (hu : (u : H) ∈ A.kerᗮ) (hAu : A u = f - A.ker.starProjection f) :
    A.greenOperator hA h f = u := by
  set g : A.domain := ⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩
  -- The difference `G f - u` lies in the kernel and in its orthogonal complement.
  have hmem : ((g - u : A.domain) : H) ∈ A.ker ⊓ A.kerᗮ :=
    ⟨coe_mem_ker_iff.2 (by rw [map_sub, apply_greenOperator, hAu, sub_self]),
      sub_mem (A.greenOperator_mem_orthogonal_ker hA h f) hu⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, Submodule.coe_sub, sub_eq_zero] at hmem
  exact hmem

/-- **`G A = 1 - Π`** on the domain of `A`. -/
@[simp]
theorem greenOperator_apply_apply [A.ker.HasOrthogonalProjection] (u : A.domain) :
    A.greenOperator hA h (A u) = u - A.ker.starProjection u := by
  obtain ⟨v, hv, hAv⟩ := exists_coe_eq_sub_starProjection u
  rw [← hv]
  refine A.greenOperator_eq_of_apply_eq hA h (hv ▸ A.ker.sub_starProjection_mem_orthogonal _) ?_
  rw [hAv, (A.ker.starProjection_apply_eq_zero_iff).2
    (hA.isFormalAdjoint.apply_mem_orthogonal_ker u), sub_zero]

/-- The Green operator vanishes on the kernel of `A`. -/
theorem greenOperator_apply_of_mem_ker {f : H} (hf : f ∈ A.ker) : A.greenOperator hA h f = 0 := by
  have := h.hasOrthogonalProjection_ker
  have h0 := A.greenOperator_eq_of_apply_eq hA h (u := 0) (Submodule.zero_mem _)
    (by rw [map_zero, Submodule.starProjection_eq_self_iff.2 hf, sub_self])
  rwa [ZeroMemClass.coe_zero] at h0

/-- The kernel of the Green operator is the kernel of `A`. -/
theorem ker_greenOperator : LinearMap.ker (A.greenOperator hA h : H →ₗ[ℂ] H) = A.ker := by
  have := h.hasOrthogonalProjection_ker
  refine le_antisymm (fun f hf ↦ ?_) fun f hf ↦ A.greenOperator_apply_of_mem_ker hA h hf
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hf
  have hA0 := A.apply_greenOperator hA h f
  have h0 : (⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩ : A.domain) = 0 :=
    Subtype.ext hf
  rw [h0, map_zero, eq_comm, sub_eq_zero] at hA0
  exact Submodule.starProjection_eq_self_iff.1 hA0.symm

/-- The range of the Green operator is `D(A) ∩ (ker A)ᗮ`. -/
theorem range_greenOperator :
    LinearMap.range (A.greenOperator hA h : H →ₗ[ℂ] H) = A.domain ⊓ A.kerᗮ := by
  have := h.hasOrthogonalProjection_ker
  refine le_antisymm ?_ fun u ⟨hu, huK⟩ ↦ ⟨A ⟨u, hu⟩, ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact ⟨A.greenOperator_mem_domain hA h f, A.greenOperator_mem_orthogonal_ker hA h f⟩
  · rw [ContinuousLinearMap.coe_coe, greenOperator_apply_apply,
      (A.ker.starProjection_apply_eq_zero_iff).2 huK, sub_zero]

/-- The Green operator vanishes exactly when the kernel of `A` is the whole space. -/
theorem greenOperator_eq_zero_iff : A.greenOperator hA h = 0 ↔ A.ker = ⊤ := by
  rw [← A.ker_greenOperator hA h, LinearMap.ker_eq_top, ← ContinuousLinearMap.toLinearMap_zero,
    ContinuousLinearMap.coe_inj]

/-- The Green operator acts on an eigenvector of `A` for a nonzero eigenvalue `μ` as multiplication
by `μ⁻¹`. -/
theorem greenOperator_apply_of_apply_eq_smul (x : A.domain) {μ : ℂ} (hμ : μ ≠ 0)
    (hx : A x = μ • (x : H)) : A.greenOperator hA h x = μ⁻¹ • (x : H) := by
  have := h.hasOrthogonalProjection_ker
  -- An eigenvector for a nonzero eigenvalue lies in the range, hence is orthogonal to the kernel.
  have hxK : (x : H) ∈ A.kerᗮ := by
    rw [← inv_smul_smul₀ hμ (x : H), ← hx]
    exact Submodule.smul_mem _ _ (hA.isFormalAdjoint.apply_mem_orthogonal_ker x)
  have hGA := A.greenOperator_apply_apply hA h x
  rw [hx, ContinuousLinearMap.map_smul, (A.ker.starProjection_apply_eq_zero_iff).2 hxK,
    sub_zero] at hGA
  exact (eq_inv_smul_iff₀ hμ).2 hGA

/-- The Green operator is self-adjoint. -/
theorem isSelfAdjoint_greenOperator : IsSelfAdjoint (A.greenOperator hA h) := by
  have := h.hasOrthogonalProjection_ker
  refine LinearMap.IsSymmetric.isSelfAdjoint fun f g ↦ ?_
  simp only [ContinuousLinearMap.coe_coe]
  -- Write `f = A (G f) + Π f` and `g = A (G g) + Π g`, and use the symmetry of `A`.
  have hf := A.apply_greenOperator hA h f
  have hg := A.apply_greenOperator hA h g
  have hGf := A.greenOperator_mem_orthogonal_ker hA h f
  have hGg := A.greenOperator_mem_orthogonal_ker hA h g
  calc ⟪A.greenOperator hA h f, g⟫_ℂ
      = ⟪A.greenOperator hA h f, (g - A.ker.starProjection g) + A.ker.starProjection g⟫_ℂ := by
        rw [sub_add_cancel]
    _ = ⟪A.greenOperator hA h f, g - A.ker.starProjection g⟫_ℂ := by
        rw [inner_add_right,
          Submodule.inner_left_of_mem_orthogonal (A.ker.starProjection_apply_mem g) hGf, add_zero]
    _ = ⟪f - A.ker.starProjection f, A.greenOperator hA h g⟫_ℂ := by
        rw [← hf, ← hg]
        exact (hA.isFormalAdjoint _ _).symm
    _ = ⟪f, A.greenOperator hA h g⟫_ℂ := by
        rw [inner_sub_left,
          Submodule.inner_right_of_mem_orthogonal (A.ker.starProjection_apply_mem f) hGg, sub_zero]

/-- The Green operator is compact: `G = R(i) (i G - 1 + Π)` for the compact resolvent `R(i)`. -/
theorem isCompactOperator_greenOperator : IsCompactOperator (A.greenOperator hA h) := by
  have := h.hasOrthogonalProjection_ker
  have hi := hA.I_mem_resolventSet
  have hG : A.greenOperator hA h = A.resolvent Complex.I ∘L
      (Complex.I • A.greenOperator hA h - ContinuousLinearMap.id ℂ H + A.ker.starProjection) := by
    ext f
    set g : A.domain := ⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩
    have hf : Complex.I • (g : H) - A g =
        Complex.I • A.greenOperator hA h f - f + A.ker.starProjection f := by
      rw [apply_greenOperator]
      abel
    simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.sub_apply,
      _root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [← hf, resolvent_smul_sub_apply hi]
  rw [hG, ContinuousLinearMap.coe_comp]
  exact (h.isCompactOperator_resolvent hi).comp_clm _

/-- **Norm bound.** If `c ‖u‖ ≤ ‖A u‖` on `D(A) ∩ (ker A)ᗮ` with `c > 0`, for instance for `c` the
least absolute value of a nonzero eigenvalue, then `‖G‖ ≤ c⁻¹`. -/
theorem norm_greenOperator_le {c : ℝ} (hc : 0 < c)
    (hbound : ∀ u : A.domain, (u : H) ∈ A.kerᗮ → c * ‖(u : H)‖ ≤ ‖A u‖) :
    ‖A.greenOperator hA h‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le)
    (norm_greenLinearMap_le hA h hc hbound)

end Complex

end LinearPMap
