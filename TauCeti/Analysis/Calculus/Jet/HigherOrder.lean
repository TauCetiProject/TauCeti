/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.CPolynomialDef
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Symmetric

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
`b` of `h`. It is computed by realizing jets by polynomial maps (`TauCeti.jetPolynomial`).
We prove that it transforms the jets of actual maps (`TauCeti.jetPullback_taylorJet`), that the
identity coordinate change acts trivially (`TauCeti.jetPullback_id`), the composition law
(`TauCeti.jetPullback_comp`), and that it commutes with truncation of jets to lower order
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
open scoped ContDiff Nat

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

/-! ### Realization of jets by polynomial maps -/

/-- The polynomial map `z ↦ ∑ₖ (k!)⁻¹ jₖ (z - c, …, z - c)` with Taylor coefficients `j` at `c`
(`TauCeti.taylorJet_jetPolynomial`). -/
def jetPolynomial (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c z : E) : F :=
  ∑ k : Fin (m + 1), ((k : ℕ)! : 𝕜)⁻¹ • j k fun _ ↦ z - c

theorem jetPolynomial_apply (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c z : E) :
    jetPolynomial j c z = ∑ k : Fin (m + 1), ((k : ℕ)! : 𝕜)⁻¹ • j k fun _ ↦ z - c :=
  (rfl)

theorem jetPolynomial_add (j₁ j₂ : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c z : E) :
    jetPolynomial (j₁ + j₂) c z = jetPolynomial j₁ c z + jetPolynomial j₂ c z := by
  simp [jetPolynomial, Finset.sum_add_distrib]

theorem jetPolynomial_smul (r : 𝕜) (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c z : E) :
    jetPolynomial (r • j) c z = r • jetPolynomial j c z := by
  simp [jetPolynomial, Finset.smul_sum, smul_comm r]

/-- Translating the centre of a jet polynomial translates its argument. -/
theorem jetPolynomial_eq_jetPolynomial_zero (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c z : E) :
    jetPolynomial j c z = jetPolynomial j 0 (z - c) := by
  simp [jetPolynomial]

/-- A jet polynomial takes the value of its jet at its centre. -/
@[simp]
theorem jetPolynomial_self (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c : E) :
    jetPolynomial j c c = j 0 0 := by
  rw [jetPolynomial, Fin.sum_univ_succ, Finset.sum_eq_zero fun k _ ↦ ?_]
  · simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, add_zero]
    exact congrArg (j 0) (funext fun i ↦ absurd i.isLt (by simp))
  · have : Nonempty (Fin (k.succ : ℕ)) := ⟨⟨0, by simp⟩⟩
    simp only [sub_self]
    rw [show (fun _ : Fin (k.succ : ℕ) ↦ (0 : E)) = 0 from rfl, (j k.succ).map_zero, smul_zero]

/-- Jet polynomials are analytic. -/
theorem contDiff_jetPolynomial (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (c : E) :
    ContDiff 𝕜 ω (jetPolynomial j c) :=
  ContDiff.sum fun k _ ↦ ((j k).contDiff.comp
    (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const)).const_smul _

/-- **Realization of jets.** The jet polynomial of a symmetric family `j` has Taylor
coefficients `j` at its centre. -/
theorem taylorJet_jetPolynomial [CharZero 𝕜] {j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F}
    (hj : j ∈ jetSpace 𝕜 E F m) (c : E) :
    taylorJet 𝕜 m (jetPolynomial j c) c = j := by
  classical
  let q : FormalMultilinearSeries 𝕜 E F := fun n ↦
    if h : n < m + 1 then ((n ! : 𝕜)⁻¹ • j ⟨n, h⟩) else 0
  have hq : HasFiniteFPowerSeriesOnBall (jetPolynomial j c) q c (m + 1) ⊤ := by
    refine HasFiniteFPowerSeriesOnBall.mk' (fun n hn ↦ ?_) ENNReal.zero_lt_top fun y _ ↦ ?_
    · simp only [q, dite_eq_right_iff]
      exact fun h ↦ absurd h (not_lt.2 hn)
    · rw [jetPolynomial, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [q, k.isLt, dite_true, Fin.eta, add_sub_cancel_left]
      rfl
  funext k
  ext v
  rw [taylorJet_apply, hq.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    ((contDiff_jetPolynomial j c).contDiffOn.analyticOn)]
  have hk : (k : ℕ) < m + 1 := k.isLt
  simp only [q, hk, dite_true, Fin.eta, smul_apply]
  simp_rw [show ∀ σ : Perm (Fin k), j k (fun i ↦ v (σ i)) = j k v from fun σ ↦
    apply_comp_perm_of_mem_jetSpace hj k σ v]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)), one_smul]

/-! ### Determinacy of jets of transformed sections -/

/-- Two maps have the same `m`-jet when their derivatives of order at most `m` agree. -/
theorem taylorJet_eq_taylorJet_iff {f₁ f₂ : E → F} {x₁ x₂ : E} :
    taylorJet 𝕜 m f₁ x₁ = taylorJet 𝕜 m f₂ x₂ ↔
      ∀ k ≤ m, iteratedFDeriv 𝕜 k f₁ x₁ = iteratedFDeriv 𝕜 k f₂ x₂ :=
  ⟨fun h k hk ↦ congrFun h ⟨k, Nat.lt_succ_of_le hk⟩,
    fun h ↦ funext fun k ↦ h k (Nat.lt_succ_iff.1 k.isLt)⟩

/-- **Jets of transformed sections.** The `m`-jet of `z ↦ g z (s (h z))` at `x` depends only on
the `m`-jets of `g` and `h` at `x` and of `s` at `h x`. -/
theorem taylorJet_clm_apply_comp_congr {g₁ g₂ : E' → F →L[𝕜] G} {h₁ h₂ : E' → E}
    {s₁ s₂ : E → F} {x : E'} (hg₁ : ContDiffAt 𝕜 m g₁ x) (hg₂ : ContDiffAt 𝕜 m g₂ x)
    (hh₁ : ContDiffAt 𝕜 m h₁ x) (hh₂ : ContDiffAt 𝕜 m h₂ x)
    (hs₁ : ContDiffAt 𝕜 m s₁ (h₁ x)) (hs₂ : ContDiffAt 𝕜 m s₂ (h₂ x))
    (hg : taylorJet 𝕜 m g₁ x = taylorJet 𝕜 m g₂ x) (hh : taylorJet 𝕜 m h₁ x = taylorJet 𝕜 m h₂ x)
    (hs : taylorJet 𝕜 m s₁ (h₁ x) = taylorJet 𝕜 m s₂ (h₂ x)) :
    taylorJet 𝕜 m (fun z ↦ g₁ z (s₁ (h₁ z))) x = taylorJet 𝕜 m (fun z ↦ g₂ z (s₂ (h₂ z))) x := by
  rw [taylorJet_eq_taylorJet_iff] at hg hh hs ⊢
  intro k hk
  have hkm : (k : ℕ∞ω) ≤ m := by exact_mod_cast hk
  -- The jets of the composites `sᵢ ∘ hᵢ` agree, by the Faà di Bruno formula.
  have hsh : ∀ i ≤ k, iteratedFDeriv 𝕜 i (s₁ ∘ h₁) x = iteratedFDeriv 𝕜 i (s₂ ∘ h₂) x :=
    fun i hi ↦ iteratedFDeriv_comp_congr (hs₁.of_le (by exact_mod_cast hi.trans hk))
      (hs₂.of_le (by exact_mod_cast hi.trans hk)) (hh₁.of_le (by exact_mod_cast hi.trans hk))
      (hh₂.of_le (by exact_mod_cast hi.trans hk)) (fun l hl ↦ hs l (hl.trans (hi.trans hk)))
      (fun l _ hl ↦ hh l (hl.trans (hi.trans hk)))
  -- Hence so do the jets of the pairs `(gᵢ, sᵢ ∘ hᵢ)`.
  have hpair : ∀ i ≤ k, iteratedFDeriv 𝕜 i (fun z ↦ (g₁ z, (s₁ ∘ h₁) z)) x =
      iteratedFDeriv 𝕜 i (fun z ↦ (g₂ z, (s₂ ∘ h₂) z)) x := fun i hi ↦ by
    have hik : (i : ℕ∞ω) ≤ m := by exact_mod_cast hi.trans hk
    rw [iteratedFDeriv_prodMk hg₁ (hs₁.comp x hh₁) hik,
      iteratedFDeriv_prodMk hg₂ (hs₂.comp x hh₂) hik, hg i (hi.trans hk), hsh i hi]
  have hx : (g₁ x, s₁ (h₁ x)) = (g₂ x, s₂ (h₂ x)) := by
    simpa using congr($(hpair 0 (Nat.zero_le _)) 0)
  -- Finally apply the evaluation map `(L, v) ↦ L v`.
  have hev : ContDiff 𝕜 ω fun p : (F →L[𝕜] G) × F ↦ p.1 p.2 :=
    isBoundedBilinearMap_apply.contDiff
  exact iteratedFDeriv_comp_congr (g₁ := fun p : (F →L[𝕜] G) × F ↦ p.1 p.2)
    (g₂ := fun p : (F →L[𝕜] G) × F ↦ p.1 p.2) (f₁ := fun z ↦ (g₁ z, (s₁ ∘ h₁) z))
    (f₂ := fun z ↦ (g₂ z, (s₂ ∘ h₂) z)) (hev.contDiffAt.of_le le_top)
    (hev.contDiffAt.of_le le_top) ((hg₁.prodMk (hs₁.comp x hh₁)).of_le hkm)
    ((hg₂.prodMk (hs₂.comp x hh₂)).of_le hkm) (fun l _ ↦ by simp only [comp_apply, hx])
    (fun l _ hl ↦ hpair l hl)

/-! ### The jet transformation -/

/-- The polynomial representative of the transformed jet in `TauCeti.jetPullback`. -/
private theorem contDiff_jetPullback_rep (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G))
    (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E) (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) :
    ContDiff 𝕜 ω fun z ↦ jetPolynomial a 0 z (jetPolynomial j (b 0 0) (jetPolynomial b 0 z)) :=
  (contDiff_jetPolynomial a 0).clm_apply
    ((contDiff_jetPolynomial j _).comp (contDiff_jetPolynomial b 0))

/-- The `m`-jet transformation for Taylor coefficients `a` of a varying linear fibre map
`g : E' → F →L[𝕜] G` and `b` of a change of base coordinates `h : E' → E`: it sends the jet of
`s : E → F` at `h x` to the jet of `z ↦ g z (s (h z))` at `x`
(`TauCeti.jetPullback_taylorJet`). It is computed on polynomial representatives centred at `0`. -/
def jetPullback (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G))
    (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E) : jetSpace 𝕜 E F m →ₗ[𝕜] jetSpace 𝕜 E' G m where
  toFun j := ⟨taylorJet 𝕜 m (fun z ↦ jetPolynomial a 0 z
      (jetPolynomial (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b 0 0) (jetPolynomial b 0 z))) 0,
    (contDiff_jetPullback_rep a b j).contDiffAt.taylorJet_mem_jetSpace le_top⟩
  map_add' j₁ j₂ := by
    refine Subtype.ext (funext fun k ↦ ?_)
    have h₁ := (contDiff_jetPullback_rep a b j₁).contDiffAt (x := 0)
    have h₂ := (contDiff_jetPullback_rep a b j₂).contDiffAt (x := 0)
    simp only [Submodule.coe_add, Pi.add_apply, taylorJet_apply, jetPolynomial_add, map_add]
    exact iteratedFDeriv_add_apply (h₁.of_le le_top) (h₂.of_le le_top)
  map_smul' r j := by
    refine Subtype.ext (funext fun k ↦ ?_)
    have h := (contDiff_jetPullback_rep a b j).contDiffAt (x := 0)
    simp only [Submodule.coe_smul, Pi.smul_apply, taylorJet_apply, jetPolynomial_smul, map_smul,
      RingHom.id_apply]
    exact iteratedFDeriv_const_smul_apply (h.of_le le_top)

theorem coe_jetPullback_apply (a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G))
    (b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E) (j : jetSpace 𝕜 E F m) :
    (jetPullback a b j : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] G) =
      taylorJet 𝕜 m (fun z ↦ jetPolynomial a 0 z
        (jetPolynomial (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b 0 0) (jetPolynomial b 0 z))) 0 :=
  (rfl)

/-- **The jet transformation on actual jets.** The `m`-jet transformation with the Taylor
coefficients of `g` and `h` at `x` sends the jet of `s` at `h x` to the jet of
`z ↦ g z (s (h z))` at `x`. -/
theorem jetPullback_taylorJet [CharZero 𝕜] {N : ℕ∞ω} {g : E' → F →L[𝕜] G} {h : E' → E}
    {s : E → F} {x : E'} (hg : ContDiffAt 𝕜 N g x) (hh : ContDiffAt 𝕜 N h x)
    (hs : ContDiffAt 𝕜 N s (h x)) (hm : minSmoothness 𝕜 m ≤ N) :
    (jetPullback (taylorJet 𝕜 m g x) (taylorJet 𝕜 m h x)
        ⟨taylorJet 𝕜 m s (h x), hs.taylorJet_mem_jetSpace hm⟩ :
        ∀ k : Fin (m + 1), E' [×k]→L[𝕜] G) =
      taylorJet 𝕜 m (fun z ↦ g z (s (h z))) x := by
  have hmN : (m : ℕ∞ω) ≤ N := le_minSmoothness.trans hm
  set a := taylorJet 𝕜 m g x
  set b := taylorJet 𝕜 m h x
  set j := taylorJet 𝕜 m s (h x)
  have hb0 : b 0 0 = h x := iteratedFDeriv_zero_apply _
  -- Replace `g`, `h` and `s` by their polynomial representatives.
  have hrep : taylorJet 𝕜 m (fun z ↦ g z (s (h z))) x = taylorJet 𝕜 m
      (fun z ↦ jetPolynomial a x z (jetPolynomial j (h x) (jetPolynomial b x z))) x := by
    have hbx : jetPolynomial b x x = h x := by rw [jetPolynomial_self, hb0]
    refine taylorJet_clm_apply_comp_congr (hg.of_le hmN)
      ((contDiff_jetPolynomial a x).contDiffAt.of_le le_top) (hh.of_le hmN)
      ((contDiff_jetPolynomial b x).contDiffAt.of_le le_top) (hs.of_le hmN)
      ((contDiff_jetPolynomial j _).contDiffAt.of_le le_top)
      (taylorJet_jetPolynomial (hg.taylorJet_mem_jetSpace hm) x).symm
      (taylorJet_jetPolynomial (hh.taylorJet_mem_jetSpace hm) x).symm ?_
    rw [hbx, taylorJet_jetPolynomial (hs.taylorJet_mem_jetSpace hm)]
  -- The representatives centred at `x` are translates of those centred at `0`.
  rw [hrep, coe_jetPullback_apply, hb0]
  simp_rw [jetPolynomial_eq_jetPolynomial_zero a x, jetPolynomial_eq_jetPolynomial_zero b x]
  funext k
  simp only [taylorJet_apply]
  rw [iteratedFDeriv_comp_sub (f := fun w ↦ jetPolynomial a 0 w
    (jetPolynomial j (h x) (jetPolynomial b 0 w))), sub_self]

/-- Every jet is the jet of its polynomial representative. -/
private theorem eq_mk_taylorJet_jetPolynomial [CharZero 𝕜] (j : jetSpace 𝕜 E F m) (c : E) :
    j = ⟨taylorJet 𝕜 m (jetPolynomial (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) c) c,
      (contDiff_jetPolynomial _ c).contDiffAt.taylorJet_mem_jetSpace le_top⟩ :=
  Subtype.ext (taylorJet_jetPolynomial j.2 c).symm

/-- The identity change of coordinates acts trivially on jets. -/
@[simp]
theorem jetPullback_id [CharZero 𝕜] (x : E) :
    jetPullback (taylorJet 𝕜 m (fun _ ↦ ContinuousLinearMap.id 𝕜 F) x) (taylorJet 𝕜 m id x) =
      LinearMap.id := by
  refine LinearMap.ext fun j ↦ ?_
  rw [eq_mk_taylorJet_jetPolynomial j x]
  refine Subtype.ext ?_
  exact jetPullback_taylorJet (N := ω) contDiffAt_const contDiffAt_id
    (contDiff_jetPolynomial _ x).contDiffAt le_top

/-- **The composition law.** Transforming a jet by `(g₁, h₁)` and then by `(g₂, h₂)` is
transforming it by the composite change of coordinates `z ↦ g₂ z ∘L g₁ (h₂ z)` and
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
  rw [eq_mk_taylorJet_jetPolynomial j (h₁ (h₂ x))]
  set S := jetPolynomial (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (h₁ (h₂ x))
  have hS : ContDiff 𝕜 ω S := contDiff_jetPolynomial _ _
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
theorem truncateJet_taylorJet {m' : ℕ} (hm : m' ≤ m) (f : E → F) (x : E) :
    truncateJet hm (taylorJet 𝕜 m f x) = taylorJet 𝕜 m' f x :=
  (rfl)

theorem truncateJet_mem_jetSpace {m' : ℕ} (hm : m' ≤ m) {j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F}
    (hj : j ∈ jetSpace 𝕜 E F m) : truncateJet hm j ∈ jetSpace 𝕜 E F m' :=
  mem_jetSpace_iff.2 fun k ↦ mem_jetSpace_iff.1 hj (Fin.castLE (Nat.succ_le_succ hm) k)

variable (𝕜 E F) in
/-- Truncation of jets to order at most `m'`, as a linear map. -/
def jetTruncate {m' : ℕ} (hm : m' ≤ m) : jetSpace 𝕜 E F m →ₗ[𝕜] jetSpace 𝕜 E F m' where
  toFun j := ⟨truncateJet hm j, truncateJet_mem_jetSpace hm j.2⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coe_jetTruncate_apply {m' : ℕ} (hm : m' ≤ m) (j : jetSpace 𝕜 E F m) :
    (jetTruncate 𝕜 E F hm j : ∀ k : Fin (m' + 1), E [×k]→L[𝕜] F) = truncateJet hm j :=
  (rfl)

private theorem taylorJet_jetPolynomial_truncateJet [CharZero 𝕜] {m' : ℕ} (hm : m' ≤ m)
    {p : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F} (hp : p ∈ jetSpace 𝕜 E F m) (c : E) :
    taylorJet 𝕜 m' (jetPolynomial p c) c =
      taylorJet 𝕜 m' (jetPolynomial (truncateJet hm p) c) c := by
  rw [← truncateJet_taylorJet hm, taylorJet_jetPolynomial hp,
    taylorJet_jetPolynomial (truncateJet_mem_jetSpace hm hp)]

/-- **Truncation commutes with the jet transformation.** For symmetric coefficients `a` and `b`,
truncating a transformed `m`-jet to order `m'` is transforming the truncated jet with the
truncated coefficients. -/
theorem jetTruncate_jetPullback [CharZero 𝕜] {m' : ℕ} (hm : m' ≤ m)
    {a : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] (F →L[𝕜] G)} {b : ∀ k : Fin (m + 1), E' [×k]→L[𝕜] E}
    (ha : a ∈ jetSpace 𝕜 E' (F →L[𝕜] G) m) (hb : b ∈ jetSpace 𝕜 E' E m) (j : jetSpace 𝕜 E F m) :
    jetTruncate 𝕜 E' G hm (jetPullback a b j) =
      jetPullback (truncateJet hm a) (truncateJet hm b) (jetTruncate 𝕜 E F hm j) := by
  refine Subtype.ext ?_
  rw [coe_jetTruncate_apply, coe_jetPullback_apply, truncateJet_taylorJet, coe_jetPullback_apply,
    coe_jetTruncate_apply]
  have hb0 : truncateJet hm b 0 0 = b 0 0 := (rfl)
  rw [hb0]
  -- Both sides are jets of order `m'` of transformed polynomial representatives, whose jets of
  -- order `m'` agree.
  have hj : taylorJet 𝕜 m' (jetPolynomial (j : ∀ k : Fin (m + 1), E [×k]→L[𝕜] F) (b 0 0))
      (jetPolynomial b 0 0) = taylorJet 𝕜 m' (jetPolynomial (truncateJet hm j.1) (b 0 0))
      (jetPolynomial (truncateJet hm b) 0 0) := by
    rw [jetPolynomial_self, jetPolynomial_self]
    exact taylorJet_jetPolynomial_truncateJet hm j.2 _
  refine taylorJet_clm_apply_comp_congr ?_ ?_ ?_ ?_ ?_ ?_
    (taylorJet_jetPolynomial_truncateJet hm ha 0) (taylorJet_jetPolynomial_truncateJet hm hb 0) hj
  all_goals exact (contDiff_jetPolynomial _ _).contDiffAt.of_le le_top

end TauCeti
