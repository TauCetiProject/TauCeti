/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Hyperfunction.Plemelj

/-!
# Distributions as one-dimensional hyperfunctions on relatively compact open sets

Let `u` be a complex-valued distribution on an open set `Ω ⊆ ℝ`, and let `V` be an open set whose
closure is a compact subset of `Ω`. For a real test function `χ` on `Ω` equal to one on `V`, the
Cauchy transform `C(z) = (2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩` is holomorphic on `ℂ ∖ ℝ`, and its class in
the space `B(V) = O(ℂ ∖ ℝ) / O(W(V))` of one-dimensional hyperfunctions on `V`, where
`W(V) = ℂ ∖ (ℝ ∖ V)`, does not depend on `χ`. This defines a complex-linear map

`TauCeti.Hyperfunction.cauchyClass V : 𝓓'(Ω) → B(V)`,

the local form of the embedding of distributions into hyperfunctions. Its properties:

* any cutoff equal to one near the points of `V` in the support of `u` computes the class
  (`TauCeti.Hyperfunction.cauchyClass_eq_mk`); in particular, when `u` has compact support in `ℝ`
  and `χ` equals one near it, `cauchyClass V u` is the restriction to `V` of the class of the
  Cauchy representative of `u` on all of `ℝ`;
* the class vanishes exactly when `u` vanishes on `V`
  (`TauCeti.Hyperfunction.cauchyClass_eq_zero_iff`), so it determines the restriction of `u` to
  `V`;
* it commutes with the restriction maps of hyperfunctions to open subsets `V' ⊆ V`
  (`TauCeti.Hyperfunction.oneDimBoundaryRestrict_cauchyClass`) and with the restriction of
  distributions to open subsets `Ω' ⊆ Ω` containing the closure of `V`
  (`TauCeti.Hyperfunction.cauchyClass_restrictCLM`).

The vanishing criterion reduces to the case of a compactly supported distribution on `ℝ`
(`Distribution.cauchyTransform_mem_throughReal_iff`) through the extension of `χ u` by zero, which
has the same Cauchy transform (`Distribution.cauchyTransform_mem_throughReal_iff_of_eqOn_one`).

## References

* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1.
* A. Kaneko, *Introduction to hyperfunctions*, Chapter 1.
-/

public section

noncomputable section

open Filter Set TopologicalSpace Distribution
open scoped Distributions Topology

namespace TauCeti.Hyperfunction

variable {Ω : Opens ℝ} (V : Opens ℝ)

/-- The **Cauchy class** on `V` of a complex-valued distribution `u` on `Ω`, for an open set `V`
whose closure is a compact subset of `Ω`: the class in the space `O(ℂ ∖ ℝ) / O(W(V))` of
one-dimensional hyperfunctions on `V` of the Cauchy transform `(2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩` with
a cutoff `χ` equal to one on `V`. It does not depend on the cutoff (`cauchyClass_eq_mk`) and it
determines the restriction of `u` to `V` (`cauchyClass_eq_zero_iff`). -/
def cauchyClass (hV : IsCompact (closure (V : Set ℝ))) (hVΩ : closure (V : Set ℝ) ⊆ Ω) :
    𝓓'(Ω, ℂ) →ₗ[ℂ] OneDimBoundaryQuotient V :=
  (throughReal V).mkQ ∘ₗ
    { toFun u := ⟨cauchyTransform u (TestFunction.exists_eventually_eq_one hV hVΩ).choose,
        cauchyTransform_mem_holomorphicSections u _⟩
      map_add' u v := Subtype.ext (cauchyTransform_add u v _)
      map_smul' c u := Subtype.ext (cauchyTransform_smul c u _) }

/-- **Independence of the cutoff.** The Cauchy class on `V` of `u` is the class of the Cauchy
transform of `u` with any cutoff equal to one near the points of `V` in the support of `u`, for
instance any cutoff equal to one on `V`, or equal to one near a compact support of `u`. -/
theorem cauchyClass_eq_mk (hV : IsCompact (closure (V : Set ℝ)))
    (hVΩ : closure (V : Set ℝ) ⊆ Ω) (u : 𝓓'(Ω, ℂ)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ t in 𝓝ˢ ((V : Set ℝ) ∩ dsupport u), χ t = 1) :
    cauchyClass V hV hVΩ u =
      Submodule.Quotient.mk ⟨cauchyTransform u χ, cauchyTransform_mem_holomorphicSections u χ⟩ := by
  refine (Submodule.Quotient.eq _).2 (cauchyTransform_sub_mem_throughReal u ?_)
  filter_upwards [(TestFunction.exists_eventually_eq_one (n := ⊤) hV hVΩ).choose_spec.1.filter_mono
    (nhdsSet_mono (inter_subset_left.trans subset_closure)), hχ] with t h₁ h₂
  rw [h₁, h₂]

/-- The Cauchy class on `V` of `u` is the class of the Cauchy transform of `u` with any cutoff
equal to one on `V`. -/
theorem cauchyClass_eq_mk_of_eqOn_one (hV : IsCompact (closure (V : Set ℝ)))
    (hVΩ : closure (V : Set ℝ) ⊆ Ω) (u : 𝓓'(Ω, ℂ)) {χ : 𝓓(Ω, ℝ)} (hχ : EqOn χ 1 V) :
    cauchyClass V hV hVΩ u =
      Submodule.Quotient.mk ⟨cauchyTransform u χ, cauchyTransform_mem_holomorphicSections u χ⟩ :=
  cauchyClass_eq_mk V hV hVΩ u <|
    eventually_of_mem (V.isOpen.mem_nhdsSet.2 inter_subset_left) fun _ ht ↦ hχ ht

/-- **The Cauchy class determines the distribution on `V`.** The Cauchy class on `V` of `u` is
zero exactly when `u` vanishes on `V`, that is, when `V` does not meet `dsupport u`. -/
theorem cauchyClass_eq_zero_iff (hV : IsCompact (closure (V : Set ℝ)))
    (hVΩ : closure (V : Set ℝ) ⊆ Ω) (u : 𝓓'(Ω, ℂ)) :
    cauchyClass V hV hVΩ u = 0 ↔ Disjoint (V : Set ℝ) (dsupport u) := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hV hVΩ
  have hχV : EqOn χ 1 V := fun t ht ↦ hχ.self_of_nhdsSet t (subset_closure ht)
  rw [cauchyClass_eq_mk_of_eqOn_one V hV hVΩ u hχV, Submodule.Quotient.mk_eq_zero,
    cauchyTransform_mem_throughReal_iff_of_eqOn_one u hχV]

/-- **Restriction of hyperfunctions.** For an open `V' ⊆ V`, the restriction to `V'` of the Cauchy
class on `V` of `u` is the Cauchy class on `V'` of `u`. -/
@[simp]
theorem oneDimBoundaryRestrict_cauchyClass (hV : IsCompact (closure (V : Set ℝ)))
    (hVΩ : closure (V : Set ℝ) ⊆ Ω) {V' : Opens ℝ} (h : V' ≤ V) (u : 𝓓'(Ω, ℂ)) :
    oneDimBoundaryRestrict h (cauchyClass V hV hVΩ u) =
      cauchyClass V' (hV.of_isClosed_subset isClosed_closure (closure_mono h))
        ((closure_mono h).trans hVΩ) u := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hV hVΩ
  have hχV : EqOn χ 1 V := fun t ht ↦ hχ.self_of_nhdsSet t (subset_closure ht)
  rw [cauchyClass_eq_mk_of_eqOn_one V hV hVΩ u hχV, oneDimBoundaryRestrict_mk,
    cauchyClass_eq_mk_of_eqOn_one V' _ _ u (hχV.mono h)]

/-- **Restriction of distributions.** For an open `Ω' ⊆ Ω` containing the closure of `V`, the
Cauchy class on `V` of the restriction `u|_{Ω'}` is the Cauchy class on `V` of `u`. -/
@[simp]
theorem cauchyClass_restrictCLM (hV : IsCompact (closure (V : Set ℝ))) {Ω' : Opens ℝ}
    (hΩ : Ω' ≤ Ω) (hVΩ' : closure (V : Set ℝ) ⊆ Ω') (u : 𝓓'(Ω, ℂ)) :
    cauchyClass V hV hVΩ' (restrictCLM u) = cauchyClass V hV (hVΩ'.trans hΩ) u := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hV hVΩ'
  have hχV : EqOn χ 1 V := fun t ht ↦ hχ.self_of_nhdsSet t (subset_closure ht)
  have hC : (⟨cauchyTransform (restrictCLM u) χ,
      cauchyTransform_mem_holomorphicSections (restrictCLM u) χ⟩ :
        holomorphicSections nonRealOpen) =
      ⟨cauchyTransform u (TestFunction.monoCLM ℝ χ),
        cauchyTransform_mem_holomorphicSections u (TestFunction.monoCLM ℝ χ)⟩ :=
    Subtype.ext (cauchyTransform_restrictCLM u χ)
  rw [cauchyClass_eq_mk_of_eqOn_one V hV hVΩ' _ hχV, hC,
    cauchyClass_eq_mk_of_eqOn_one V hV _ u (χ := TestFunction.monoCLM ℝ χ) fun t ht ↦ by
      simp [TestFunction.monoCLM_apply, hΩ, hχV ht]]

end TauCeti.Hyperfunction
