/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Symmetric
public import TauCeti.Analysis.Calculus.Jet.Realization

/-!
# Higher-order jet coordinate transformations

The local `m`-jet of a map `s : E → F` at a point is the family of its Taylor coefficients
`(Dᵏ s)` for `k ≤ m`, a family of symmetric `k`-linear maps. These families form the subspace
`TauCeti.jetSpace 𝕜 E F m` of `∀ k : Fin (m + 1), E [×k]→L[𝕜] F`; this is the model fibre of the
bundle of `m`-jets of sections of a vector bundle with fibre `F` over a manifold modelled on `E`.

Under a change of base coordinates `h` and a varying linear fibre map `g`, a section `s` becomes
`z ↦ g z (s (h z))`. Its `m`-jet at `x` is determined by the `m`-jets of `g` and `h` at `x` and of
`s` at `h x` (`TauCeti.taylorJet_clm_apply_comp_congr`), and depends linearly on the jet of `s`.
`TauCeti.jetPullback a b` is this linear transformation, for Taylor coefficients `a` of `g` and
`b` of `h`. It is computed by realizing jets by the polynomial maps
`TauCeti.finiteJetPolynomial`. Over a field of characteristic zero, we prove that it transforms
the jets of actual maps (`TauCeti.jetPullback_taylorJet`), that the identity coordinate change
acts trivially (`TauCeti.jetPullback_id`) and the composition law (`TauCeti.jetPullback_comp`);
the maps should be `Cᵐ` over `ℝ` or `ℂ` and analytic otherwise (`minSmoothness 𝕜 m ≤ N`). Over
any field, it commutes with truncation of jets to lower order
(`TauCeti.jetTruncate_jetPullback`).

These are the local coordinate results from which the bundle of `m`-jets of a vector bundle is
glued, with the coordinate changes of the bundle and the changes of charts of the base.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §§12.2–12.5 and 12.16–12.17.
-/

public section

noncomputable section

open Equiv Function
open scoped ContDiff Nat Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {m : ℕ}

/-! ### Jets as symmetric Taylor coefficients -/

variable (𝕜 E F) in
/-- The space of `m`-jets of maps `E → F` at a point: families of symmetric `k`-linear maps for
`k ≤ m`, the Taylor coefficients of order at most `m`. -/
def jetSpace (m : ℕ) : Submodule 𝕜 (∀ k : Fin (m + 1), E [×k]→L[𝕜] F) where
  carrier := {j | ∀ (k : Fin (m + 1)) (σ : Perm (Fin k)), (j k).domDomCongr σ = j k}
  add_mem' {j₁ j₂} h₁ h₂ k σ := by
    ext v
    simpa using congr($(congr($(h₁ k σ) v)) + $(congr($(h₂ k σ) v)))
  zero_mem' k σ := by
    ext v
    simp
  smul_mem' c j h k σ := by
    ext v
    simpa using congr(c • $(congr($(h k σ) v)))

/-- A family of Taylor coefficients is a jet when each coefficient is symmetric. -/
theorem mem_jetSpace_iff {j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F} :
    j ∈ jetSpace 𝕜 E F m ↔ ∀ (k : Fin (m + 1)) (σ : Perm (Fin k)), (j k).domDomCongr σ = j k :=
  Iff.rfl

/-- The coefficients of a jet do not depend on the order of their arguments. -/
theorem apply_comp_perm_of_mem_jetSpace {j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F}
    (hj : j ∈ jetSpace 𝕜 E F m) (k : Fin (m + 1)) (σ : Perm (Fin k)) (v : Fin k → E) :
    j k (v ∘ σ) = j k v :=
  congr($(mem_jetSpace_iff.1 hj k σ) v)

variable (𝕜 m) in
/-- The Taylor coefficients of `f` at `x` of order at most `m`: the truncation of
`ftaylorSeries 𝕜 f x`. -/
def taylorJet (f : E → F) (x : E) : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F :=
  fun k ↦ ftaylorSeries 𝕜 f x k

@[simp]
theorem taylorJet_apply (f : E → F) (x : E) (k : Fin (m + 1)) :
    taylorJet 𝕜 m f x k = iteratedFDeriv 𝕜 k f x :=
  (rfl)

/-- The Taylor coefficients of a map which is `Cᵐ` at `x` are symmetric (over a field other than
`ℝ` or `ℂ`, the map should be analytic). -/
theorem _root_.ContDiffAt.taylorJet_mem_jetSpace {N : ℕ∞ω} {f : E → F} {x : E}
    (hf : ContDiffAt 𝕜 N f x) (hm : minSmoothness 𝕜 m ≤ N) :
    taylorJet 𝕜 m f x ∈ jetSpace 𝕜 E F m := mem_jetSpace_iff.2 fun k σ ↦
  hf.domDomCongr_iteratedFDeriv_of_minSmoothness_le
    ((minSmoothness_monotone (Nat.cast_le.2 (Nat.lt_succ_iff.1 k.isLt))).trans hm) σ

/-- The space of jets is closed. -/
instance : IsClosed (jetSpace 𝕜 E F m : Set (∀ k : Fin (m + 1), E [×k]→L[𝕜] F)) := by
  have h : (jetSpace 𝕜 E F m : Set (∀ k : Fin (m + 1), E [×k]→L[𝕜] F)) =
      ⋂ (k : Fin (m + 1)) (σ : Perm (Fin k)), {j | (j k).domDomCongr σ = j k} := by
    ext j
    simp [mem_jetSpace_iff]
  rw [h]
  -- The isometry `domDomCongrₗᵢ 𝕜 E F σ` is `domDomCongr σ` by definition.
  exact isClosed_iInter fun k ↦ isClosed_iInter fun σ ↦ isClosed_eq
    ((ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E F σ).continuous.comp (continuous_apply k))
    (continuous_apply k)

/-- The jet of a map at `x` only depends on its germ at `x`. -/
theorem _root_.Filter.EventuallyEq.taylorJet_eq {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    taylorJet 𝕜 m f₁ x = taylorJet 𝕜 m f₂ x :=
  funext fun k ↦ (h.iteratedFDeriv 𝕜 k).eq_of_nhds

@[simp]
theorem taylorJet_zero (x : E) : taylorJet 𝕜 m (0 : E → F) x = 0 :=
  funext fun k ↦ by simp

/-- Taylor jets of maps which are `Cᵐ` at `x` are additive. -/
theorem taylorJet_add {f₁ f₂ : E → F} {x : E} (h₁ : ContDiffAt 𝕜 m f₁ x)
    (h₂ : ContDiffAt 𝕜 m f₂ x) :
    taylorJet 𝕜 m (f₁ + f₂) x = taylorJet 𝕜 m f₁ x + taylorJet 𝕜 m f₂ x :=
  funext fun k ↦ iteratedFDeriv_add_apply (h₁.of_le (by exact_mod_cast Nat.lt_succ_iff.1 k.isLt))
    (h₂.of_le (by exact_mod_cast Nat.lt_succ_iff.1 k.isLt))

/-- Taylor jets are homogeneous. -/
theorem taylorJet_const_smul (c : 𝕜) (f : E → F) (x : E) :
    taylorJet 𝕜 m (c • f) x = c • taylorJet 𝕜 m f x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  -- Multiplication by `c ≠ 0` is a continuous linear equivalence.
  funext k
  ext v
  let L := ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (M₁ := F) (Units.mk0 c hc)
  have hL : L ∘ f = c • f := funext fun y ↦ by simp [L, Units.smul_def]
  have h := L.iteratedFDeriv_comp_left (f := f) (x := x) (i := k)
  rw [hL] at h
  simpa [L, Units.smul_def] using congr($h v)

/-! ### Realization of jets by polynomial maps -/

/-- **Realization of jets.** Over a field of characteristic zero, the finite Taylor polynomial
`TauCeti.finiteJetPolynomial` of a jet `j` has Taylor coefficients `j` at its centre. -/
@[simp]
theorem taylorJet_finiteJetPolynomial [CharZero 𝕜] {j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F}
    (hj : j ∈ jetSpace 𝕜 E F m) (c : E) :
    taylorJet 𝕜 m (finiteJetPolynomial m j c) c = j :=
  funext fun k ↦ iteratedFDeriv_finiteJetPolynomial_self m j c k
    fun v σ ↦ apply_comp_perm_of_mem_jetSpace hj k σ v

/-! ### Determinacy of jets of transformed sections -/

/-- Two maps have the same `m`-jet when their derivatives of order at most `m` agree. -/
theorem taylorJet_eq_taylorJet_iff {f₁ f₂ : E → F} {x₁ x₂ : E} :
    taylorJet 𝕜 m f₁ x₁ = taylorJet 𝕜 m f₂ x₂ ↔
      ∀ k ≤ m, iteratedFDeriv 𝕜 k f₁ x₁ = iteratedFDeriv 𝕜 k f₂ x₂ :=
  ⟨fun h k hk ↦ congrFun h ⟨k, Nat.lt_succ_of_le hk⟩,
    fun h ↦ funext fun k ↦ h k (Nat.lt_succ_iff.1 k.isLt)⟩

/-- **Jets of transformed sections.** If `gᵢ` and `hᵢ` are `Cᵐ` at `xᵢ` and `sᵢ` is `Cᵐ` at
`hᵢ xᵢ`, then the `m`-jet of `z ↦ gᵢ z (sᵢ (hᵢ z))` at `xᵢ` depends only on the `m`-jets of `gᵢ`
and `hᵢ` at `xᵢ` and of `sᵢ` at `hᵢ xᵢ`. -/
theorem taylorJet_clm_apply_comp_congr {g₁ g₂ : E' → F →L[𝕜] G} {h₁ h₂ : E' → E}
    {s₁ s₂ : E → F} {x₁ x₂ : E'} (hg₁ : ContDiffAt 𝕜 m g₁ x₁) (hg₂ : ContDiffAt 𝕜 m g₂ x₂)
    (hh₁ : ContDiffAt 𝕜 m h₁ x₁) (hh₂ : ContDiffAt 𝕜 m h₂ x₂)
    (hs₁ : ContDiffAt 𝕜 m s₁ (h₁ x₁)) (hs₂ : ContDiffAt 𝕜 m s₂ (h₂ x₂))
    (hg : taylorJet 𝕜 m g₁ x₁ = taylorJet 𝕜 m g₂ x₂)
    (hh : taylorJet 𝕜 m h₁ x₁ = taylorJet 𝕜 m h₂ x₂)
    (hs : taylorJet 𝕜 m s₁ (h₁ x₁) = taylorJet 𝕜 m s₂ (h₂ x₂)) :
    taylorJet 𝕜 m (fun z ↦ g₁ z (s₁ (h₁ z))) x₁ =
      taylorJet 𝕜 m (fun z ↦ g₂ z (s₂ (h₂ z))) x₂ := by
  rw [taylorJet_eq_taylorJet_iff] at hg hh hs ⊢
  intro k hk
  have hkm : (k : ℕ∞ω) ≤ m := by exact_mod_cast hk
  -- The jets of the composites `sᵢ ∘ hᵢ` agree, by the Faà di Bruno formula.
  have hsh : ∀ i ≤ k, iteratedFDeriv 𝕜 i (s₁ ∘ h₁) x₁ = iteratedFDeriv 𝕜 i (s₂ ∘ h₂) x₂ :=
    fun i hi ↦ iteratedFDeriv_comp_congr (hs₁.of_le (by exact_mod_cast hi.trans hk))
      (hs₂.of_le (by exact_mod_cast hi.trans hk)) (hh₁.of_le (by exact_mod_cast hi.trans hk))
      (hh₂.of_le (by exact_mod_cast hi.trans hk)) (fun l hl ↦ hs l (hl.trans (hi.trans hk)))
      (fun l _ hl ↦ hh l (hl.trans (hi.trans hk)))
  -- Hence so do the jets of the pairs `(gᵢ, sᵢ ∘ hᵢ)`.
  have hpair : ∀ i ≤ k, iteratedFDeriv 𝕜 i (fun z ↦ (g₁ z, (s₁ ∘ h₁) z)) x₁ =
      iteratedFDeriv 𝕜 i (fun z ↦ (g₂ z, (s₂ ∘ h₂) z)) x₂ := fun i hi ↦ by
    have hik : (i : ℕ∞ω) ≤ m := by exact_mod_cast hi.trans hk
    rw [iteratedFDeriv_prodMk hg₁ (hs₁.comp x₁ hh₁) hik,
      iteratedFDeriv_prodMk hg₂ (hs₂.comp x₂ hh₂) hik, hg i (hi.trans hk), hsh i hi]
  have hx : (g₁ x₁, s₁ (h₁ x₁)) = (g₂ x₂, s₂ (h₂ x₂)) := by
    simpa using congr($(hpair 0 (Nat.zero_le _)) 0)
  -- Finally apply the evaluation map `(L, v) ↦ L v`.
  have hev : ContDiff 𝕜 ω fun p : (F →L[𝕜] G) × F ↦ p.1 p.2 :=
    isBoundedBilinearMap_apply.contDiff
  exact iteratedFDeriv_comp_congr (g₁ := fun p : (F →L[𝕜] G) × F ↦ p.1 p.2)
    (g₂ := fun p : (F →L[𝕜] G) × F ↦ p.1 p.2) (f₁ := fun z ↦ (g₁ z, (s₁ ∘ h₁) z))
    (f₂ := fun z ↦ (g₂ z, (s₂ ∘ h₂) z)) (hev.contDiffAt.of_le le_top)
    (hev.contDiffAt.of_le le_top) ((hg₁.prodMk (hs₁.comp x₁ hh₁)).of_le hkm)
    ((hg₂.prodMk (hs₂.comp x₂ hh₂)).of_le hkm) (fun l _ ↦ by simp only [comp_apply, hx])
    (fun l _ hl ↦ hpair l hl)

/-! ### The jet transformation -/

/-- The polynomial representative of the transformed jet in `TauCeti.jetPullback`. -/
private theorem contDiff_jetPullback_rep (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G))
    (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E) (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) :
    ContDiff 𝕜 ω fun z ↦
      finiteJetPolynomial m a 0 z (finiteJetPolynomial m j (b 0 0) (finiteJetPolynomial m b 0 z)) :=
  (contDiff_finiteJetPolynomial m a 0).clm_apply
    ((contDiff_finiteJetPolynomial m j _).comp (contDiff_finiteJetPolynomial m b 0))

/-- The `m`-jet transformation for Taylor coefficients `a` of a varying linear fibre map
`g : E' → F →L[𝕜] G` and `b` of a change of base coordinates `h : E' → E`: over a field of
characteristic zero, it sends the jet of `s : E → F` at `h x` to the jet of `z ↦ g z (s (h z))`
at `x` (`TauCeti.jetPullback_taylorJet`). It is computed on polynomial representatives centred
at `0`. -/
def jetPullback (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G))
    (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E) : jetSpace 𝕜 E F m →ₗ[𝕜] jetSpace 𝕜 E' G m where
  toFun j := ⟨taylorJet 𝕜 m (fun z ↦ finiteJetPolynomial m a 0 z
      (finiteJetPolynomial m (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b 0 0)
        (finiteJetPolynomial m b 0 z))) 0,
    (contDiff_jetPullback_rep a b j).contDiffAt.taylorJet_mem_jetSpace le_top⟩
  map_add' j₁ j₂ := by
    refine Subtype.ext (funext fun k ↦ ?_)
    have h₁ := (contDiff_jetPullback_rep a b j₁).contDiffAt (x := 0)
    have h₂ := (contDiff_jetPullback_rep a b j₂).contDiffAt (x := 0)
    simp only [Submodule.coe_add, Pi.add_apply, taylorJet_apply, finiteJetPolynomial_add,
      map_add]
    exact iteratedFDeriv_add_apply (h₁.of_le le_top) (h₂.of_le le_top)
  map_smul' r j := by
    refine Subtype.ext (funext fun k ↦ ?_)
    have h := (contDiff_jetPullback_rep a b j).contDiffAt (x := 0)
    simp only [Submodule.coe_smul, Pi.smul_apply, taylorJet_apply, finiteJetPolynomial_smul,
      map_smul, RingHom.id_apply]
    exact iteratedFDeriv_const_smul_apply (h.of_le le_top)

theorem coe_jetPullback_apply (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G))
    (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E) (j : jetSpace 𝕜 E F m) :
    (jetPullback a b j : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] G) =
      taylorJet 𝕜 m (fun z ↦ finiteJetPolynomial m a 0 z
        (finiteJetPolynomial m (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b 0 0)
          (finiteJetPolynomial m b 0 z))) 0 :=
  (rfl)

/-- The jet transformation does not depend on the coefficient `b 0` of order zero, that is, on
the base point `h x`: only the derivatives of the change of coordinates enter. -/
theorem jetPullback_congr (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G))
    {b₁ b₂ : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E} (hb : ∀ k, k ≠ 0 → b₁ k = b₂ k) :
    jetPullback a b₁ = jetPullback a b₂ := by
  refine LinearMap.ext fun j ↦ Subtype.ext ?_
  have key (z : E') :
      finiteJetPolynomial m b₁ 0 z - b₁ 0 0 = finiteJetPolynomial m b₂ 0 z - b₂ 0 0 := by
    have h0 (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E) : b 0 (fun _ ↦ z - 0) = b 0 0 :=
      congrArg (b 0) (funext fun i ↦ absurd i.isLt (by simp))
    simp only [finiteJetPolynomial_apply, Fin.sum_univ_succ, hb _ (Fin.succ_ne_zero _), h0]
    simp
  rw [coe_jetPullback_apply, coe_jetPullback_apply]
  congr 1
  funext z
  rw [finiteJetPolynomial_apply m (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b₁ 0 0),
    finiteJetPolynomial_apply m (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b₂ 0 0), key z]

/-- **The jet transformation on actual jets.** Over a field of characteristic zero, the `m`-jet
transformation with the Taylor coefficients of `g` and `h` at `x` sends the jet of `s` at `h x`
to the jet of `z ↦ g z (s (h z))` at `x`, provided `g`, `h` and `s` are `Cᵐ` over `ℝ` or `ℂ`
(analytic over other fields). -/
theorem jetPullback_taylorJet [CharZero 𝕜] {N : ℕ∞ω} {g : E' → F →L[𝕜] G} {h : E' → E}
    {s : E → F} {x : E'} (hg : ContDiffAt 𝕜 N g x) (hh : ContDiffAt 𝕜 N h x)
    (hs : ContDiffAt 𝕜 N s (h x)) (hm : minSmoothness 𝕜 m ≤ N) :
    (jetPullback (taylorJet 𝕜 m g x) (taylorJet 𝕜 m h x)
        ⟨taylorJet 𝕜 m s (h x), hs.taylorJet_mem_jetSpace hm⟩ :
        ∀ k : Fin (m + 1), E' [×k]→L[𝕜] G) =
      taylorJet 𝕜 m (fun z ↦ g z (s (h z))) x := by
  have hmN : (m : ℕ∞ω) ≤ N := le_minSmoothness.trans hm
  have hb0 : taylorJet 𝕜 m h x 0 0 = h x := iteratedFDeriv_zero_apply _
  rw [coe_jetPullback_apply, hb0]
  -- The polynomial representatives centred at `0` have the jets at `0` of `g`, `h` and `s`.
  refine taylorJet_clm_apply_comp_congr (contDiff_finiteJetPolynomial _ _ _).contDiffAt
    (hg.of_le hmN) (contDiff_finiteJetPolynomial _ _ _).contDiffAt (hh.of_le hmN)
    (contDiff_finiteJetPolynomial _ _ _).contDiffAt (hs.of_le hmN)
    (taylorJet_finiteJetPolynomial (hg.taylorJet_mem_jetSpace hm) 0)
    (taylorJet_finiteJetPolynomial (hh.taylorJet_mem_jetSpace hm) 0) ?_
  rw [finiteJetPolynomial_self, hb0, taylorJet_finiteJetPolynomial (hs.taylorJet_mem_jetSpace hm)]

/-- Every jet is the jet of its polynomial representative. -/
private theorem eq_mk_taylorJet_finiteJetPolynomial [CharZero 𝕜] (j : jetSpace 𝕜 E F m) (c : E) :
    j = ⟨taylorJet 𝕜 m (finiteJetPolynomial m (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) c) c,
      (contDiff_finiteJetPolynomial _ _ c).contDiffAt.taylorJet_mem_jetSpace le_top⟩ :=
  Subtype.ext (taylorJet_finiteJetPolynomial j.2 c).symm

/-- Over a field of characteristic zero, the identity change of coordinates acts trivially on
jets. -/
@[simp]
theorem jetPullback_id [CharZero 𝕜] (x : E) :
    jetPullback (taylorJet 𝕜 m (fun _ ↦ ContinuousLinearMap.id 𝕜 F) x) (taylorJet 𝕜 m id x) =
      LinearMap.id := by
  refine LinearMap.ext fun j ↦ ?_
  rw [eq_mk_taylorJet_finiteJetPolynomial j x]
  refine Subtype.ext ?_
  exact jetPullback_taylorJet (N := ω) contDiffAt_const contDiffAt_id
    (contDiff_finiteJetPolynomial _ _ x).contDiffAt le_top

/-- **The composition law.** Over a field of characteristic zero, and for maps which are `Cᵐ`
over `ℝ` or `ℂ` (analytic over other fields), transforming a jet by `(g₁, h₁)` and then by
`(g₂, h₂)` is transforming it by the composite change of coordinates `z ↦ g₂ z ∘L g₁ (h₂ z)` and
`h₁ ∘ h₂`. -/
theorem jetPullback_comp [CharZero 𝕜] {N : ℕ∞ω} {g₁ : E' → F →L[𝕜] G} {h₁ : E' → E}
    {g₂ : E'' → G →L[𝕜] H} {h₂ : E'' → E'} {x : E''} (hg₁ : ContDiffAt 𝕜 N g₁ (h₂ x))
    (hh₁ : ContDiffAt 𝕜 N h₁ (h₂ x)) (hg₂ : ContDiffAt 𝕜 N g₂ x) (hh₂ : ContDiffAt 𝕜 N h₂ x)
    (hm : minSmoothness 𝕜 m ≤ N) :
    (jetPullback (taylorJet 𝕜 m g₂ x) (taylorJet 𝕜 m h₂ x)).comp
        (jetPullback (taylorJet 𝕜 m g₁ (h₂ x)) (taylorJet 𝕜 m h₁ (h₂ x))) =
      jetPullback (taylorJet 𝕜 m (fun z ↦ (g₂ z).comp (g₁ (h₂ z))) x)
        (taylorJet 𝕜 m (h₁ ∘ h₂) x) := by
  refine LinearMap.ext fun j ↦ ?_
  rw [eq_mk_taylorJet_finiteJetPolynomial j (h₁ (h₂ x))]
  set S := finiteJetPolynomial m (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (h₁ (h₂ x))
  have hS : ContDiff 𝕜 ω S := contDiff_finiteJetPolynomial _ _ _
  have hS₁ : ContDiffAt 𝕜 N (fun z ↦ g₁ z (S (h₁ z))) (h₂ x) :=
    hg₁.clm_apply ((hS.contDiffAt.of_le le_top).comp _ hh₁)
  have h₁j : jetPullback (taylorJet 𝕜 m g₁ (h₂ x)) (taylorJet 𝕜 m h₁ (h₂ x))
      ⟨taylorJet 𝕜 m S (h₁ (h₂ x)), hS.contDiffAt.taylorJet_mem_jetSpace le_top⟩ =
      ⟨taylorJet 𝕜 m (fun z ↦ g₁ z (S (h₁ z))) (h₂ x), hS₁.taylorJet_mem_jetSpace hm⟩ :=
    Subtype.ext (jetPullback_taylorJet hg₁ hh₁ (hS.contDiffAt.of_le le_top) hm)
  refine Subtype.ext ?_
  rw [LinearMap.comp_apply, h₁j, jetPullback_taylorJet hg₂ hh₂ hS₁ hm]
  exact (jetPullback_taylorJet (s := S) (hg₂.clm_comp (hg₁.comp x hh₂)) (hh₁.comp x hh₂)
    (hS.contDiffAt.of_le le_top) hm).symm

/-! ### Truncation -/

/-- Truncation of the Taylor coefficients to order at most `m'`. -/
def truncateJet {m' : ℕ} (hm : m' ≤ m) (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) :
    ∀ k : Fin (m' + 1), E [×k]→L[𝕜] F :=
  fun k ↦ j (Fin.castLE (Nat.succ_le_succ hm) k)

@[simp]
theorem truncateJet_apply {m' : ℕ} (hm : m' ≤ m) (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F)
    (k : Fin (m' + 1)) : truncateJet hm j k = j (Fin.castLE (Nat.succ_le_succ hm) k) :=
  (rfl)

@[simp]
theorem truncateJet_rfl (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) : truncateJet le_rfl j = j :=
  (rfl)

/-- Truncating twice is truncating once. -/
@[simp]
theorem truncateJet_truncateJet {m' m'' : ℕ} (hm' : m'' ≤ m') (hm : m' ≤ m)
    (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) :
    truncateJet hm' (truncateJet hm j) = truncateJet (hm'.trans hm) j :=
  (rfl)

@[simp]
theorem truncateJet_taylorJet {m' : ℕ} (hm : m' ≤ m) (f : E → F) (x : E) :
    truncateJet hm (taylorJet 𝕜 m f x) = taylorJet 𝕜 m' f x :=
  (rfl)

theorem truncateJet_mem_jetSpace {m' : ℕ} (hm : m' ≤ m) {j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F}
    (hj : j ∈ jetSpace 𝕜 E F m) : truncateJet hm j ∈ jetSpace 𝕜 E F m' :=
  mem_jetSpace_iff.2 fun k ↦ mem_jetSpace_iff.1 hj (Fin.castLE (Nat.succ_le_succ hm) k)

variable (𝕜 E F) in
/-- Truncation of jets to order at most `m'`, as a continuous linear map. -/
def jetTruncate {m' : ℕ} (hm : m' ≤ m) : jetSpace 𝕜 E F m →L[𝕜] jetSpace 𝕜 E F m' where
  toFun j := ⟨truncateJet hm j, truncateJet_mem_jetSpace hm j.2⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  cont := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_pi fun k ↦ (continuous_apply _).comp continuous_subtype_val

@[simp]
theorem coe_jetTruncate_apply {m' : ℕ} (hm : m' ≤ m) (j : jetSpace 𝕜 E F m) :
    (jetTruncate 𝕜 E F hm j : ∀ k : Fin (m' + 1), E [×k]→L[𝕜] F) = truncateJet hm j :=
  (rfl)

@[simp]
theorem jetTruncate_rfl : jetTruncate 𝕜 E F (le_refl m) = ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext fun _ ↦ (rfl)

/-- Truncating twice is truncating once. -/
@[simp]
theorem jetTruncate_comp {m' m'' : ℕ} (hm' : m'' ≤ m') (hm : m' ≤ m) :
    (jetTruncate 𝕜 E F hm').comp (jetTruncate 𝕜 E F hm) = jetTruncate 𝕜 E F (hm'.trans hm) :=
  ContinuousLinearMap.ext fun _ ↦ (rfl)

/-- The jet of order `m' ≤ m` of the finite Taylor polynomial of `p` at its centre only depends
on the coefficients of `p` of order at most `m'`. -/
theorem taylorJet_finiteJetPolynomial_truncateJet {m' : ℕ} (hm : m' ≤ m)
    (p : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c : E) :
    taylorJet 𝕜 m' (finiteJetPolynomial m p c) c =
      taylorJet 𝕜 m' (finiteJetPolynomial m' (truncateJet hm p) c) c := by
  funext k
  ext v
  exact (iteratedFDeriv_finiteJetPolynomial_self_apply m p c (Fin.castLE _ k) v).trans
    (iteratedFDeriv_finiteJetPolynomial_self_apply m' (truncateJet hm p) c k v).symm

/-- Over a field of characteristic zero, the jet of order `m' ≤ m` of the finite Taylor
polynomial of a jet `p` at its centre is the truncation of `p`. -/
theorem taylorJet_finiteJetPolynomial_of_le [CharZero 𝕜] {m' : ℕ} (hm : m' ≤ m)
    {p : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F} (hp : p ∈ jetSpace 𝕜 E F m) (c : E) :
    taylorJet 𝕜 m' (finiteJetPolynomial m p c) c = truncateJet hm p := by
  rw [taylorJet_finiteJetPolynomial_truncateJet hm,
    taylorJet_finiteJetPolynomial (truncateJet_mem_jetSpace hm hp)]

/-- **Truncation commutes with the jet transformation.** Truncating a transformed `m`-jet to
order `m'` is transforming the truncated jet with the truncated coefficients. -/
theorem jetTruncate_jetPullback {m' : ℕ} (hm : m' ≤ m)
    (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G)) (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E)
    (j : jetSpace 𝕜 E F m) :
    jetTruncate 𝕜 E' G hm (jetPullback a b j) =
      jetPullback (truncateJet hm a) (truncateJet hm b) (jetTruncate 𝕜 E F hm j) := by
  refine Subtype.ext ?_
  rw [coe_jetTruncate_apply, coe_jetPullback_apply, truncateJet_taylorJet, coe_jetPullback_apply,
    coe_jetTruncate_apply]
  have hb0 : truncateJet hm b 0 0 = b 0 0 := (rfl)
  rw [hb0]
  -- Both sides are jets of order `m'` of transformed polynomial representatives, whose jets of
  -- order `m'` agree.
  have hj : taylorJet 𝕜 m' (finiteJetPolynomial m (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b 0 0))
      (finiteJetPolynomial m b 0 0) =
      taylorJet 𝕜 m' (finiteJetPolynomial m' (truncateJet hm j.1) (b 0 0))
        (finiteJetPolynomial m' (truncateJet hm b) 0 0) := by
    rw [finiteJetPolynomial_self, finiteJetPolynomial_self, hb0]
    exact taylorJet_finiteJetPolynomial_truncateJet hm _ _
  refine taylorJet_clm_apply_comp_congr ?_ ?_ ?_ ?_ ?_ ?_
    (taylorJet_finiteJetPolynomial_truncateJet hm a 0)
    (taylorJet_finiteJetPolynomial_truncateJet hm b 0) hj
  all_goals exact (contDiff_finiteJetPolynomial _ _ _).contDiffAt

end TauCeti
