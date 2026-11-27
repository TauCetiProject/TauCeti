/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Gray
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Opens

/-!
# Interpolating contact forms which agree along a set

Let `α₀` and `α₁` be one-forms on a finite-dimensional manifold `M` and let `K ⊆ M` be a set along
which they agree to first order on the contact hyperplanes: at each `x ∈ K`, `α₀` is contact,
`α₁ x = α₀ x`, and `dα₁ x` agrees with `dα₀ x` on `ker α₀ x × ker α₀ x`. Then every form of the
linear interpolation `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, takes the value `α₀ x` at `x ∈ K`, and its
exterior derivative agrees with `dα₀ x` on `ker α₀ x`, so it is contact at `x`
(`TauCeti.SmoothForm.isContactFormAt_add_smul_sub`). This persists when the exterior derivatives
agree only on pairs with one vector in a subspace `W ⊆ ker α₀ x` containing its own
`dα₀ x`-orthogonal in `ker α₀ x`, such as the tangent space of a Legendrian submanifold
(`TauCeti.SmoothForm.isContactFormAt_add_smul_sub_of_mextDeriv_eq_on`). The contact condition is
open in the parameter and the point
(`TauCeti.SmoothForm.isOpen_setOf_isContactFormAt_mpullback_prodMk`), and `[0, 1]` is compact, so
the whole interpolation is contact on an open neighbourhood of `K`
(`TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub`). No compactness of `K` is
needed, since only the parameter interval is compact.

The same holds when `α₁` agrees with `α₀` along `K` only up to a positive function `c`:
`α₁ x = c x α₀ x` and `dα₁ x = c x dα₀ x` on `ker α₀ x`. The interpolation then takes the value
`(1 + s (c x - 1)) α₀ x` at `x ∈ K`, a positive multiple of `α₀ x` for `s ∈ [0, 1]`
(`TauCeti.SmoothForm.isContactFormAt_add_smul_sub_of_eq_smul`,
`TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub_of_eq_smul`). This is the
form of the comparison in which the two contact lines along `K` are identified by a positive
factor rather than equal.

On this neighbourhood the interpolation, reparametrized by a smooth step function, is a smooth
family of contact forms whose hyperplanes do not move along `K`. Relative Gray stability
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul`) on the open submanifold then
gives a partial diffeomorphism of `M`, defined on open neighbourhoods of `K`, which fixes every
point of `K` and pulls `α₁` back to a positive multiple of `α₀`
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`, and
`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_eq_smul` up to a positive
factor). So contact structures whose defining forms have the same values and the same Levi forms
along `K`, up to a positive factor, agree near `K` up to a contactomorphism fixing `K`. This is the
step of the isotropic and Legendrian neighbourhood theorems which compares two contact structures
after their first-order data along the submanifold have been identified.

## Main results

* `TauCeti.SmoothForm.isContactFormAt_add_smul_sub`: the interpolations are contact along `K`.
* `TauCeti.SmoothForm.isContactFormAt_add_smul_sub_of_mextDeriv_eq_on`: the same when the exterior
  derivatives only agree on pairs with one vector in a coisotropic subspace of `ker α₀`, such as the
  tangent space of a Legendrian submanifold.
* `TauCeti.SmoothForm.isContactFormAt_add_smul_sub_of_eq_smul`: the interpolations are contact
  at a point where the first-order data agree up to a positive factor.
* `TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub_of_isContactFormAt`: if
  the interpolations `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, are contact along `K`, they are contact on an
  open neighbourhood of `K`.
* `TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub`,
  `TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub_of_eq_smul`: this holds
  for forms agreeing to first order along `K`, exactly or up to a positive factor.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_forall_isContactFormAt`:
  relative Gray stability for two forms joined by a segment of contact forms, the second a
  multiple of the first along `K`.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`,
  `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_eq_smul`: relative Gray
  stability for two contact forms agreeing to first order along `K`, exactly or up to a positive
  factor.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and Section 2.5 (the isotropic neighbourhood theorem, whose
  proof interpolates two contact forms agreeing along the submanifold).
-/

public section

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α₀ α₁ : SmoothForm I M ℝ 1}

/-! ### The interpolation is contact near the set of agreement -/

/-- **Interpolations of forms agreeing along a coisotropic subspace are contact.** Let `α₀` be
contact at `x` and `α₁ x = α₀ x`, and let `W ⊆ ker α₀ x` be a subspace containing every vector of
`ker α₀ x` that is `dα₀ x`-orthogonal to `W`. If `dα₁ x (w, v) = dα₀ x (w, v)` for `w ∈ W` and
`v ∈ ker α₀ x`, then every form `α₀ + s (α₁ - α₀)` is contact at `x`. The exterior derivatives may
differ on pairs of vectors outside `W`; for the tangent space `W` of a Legendrian submanifold
through `x` this asks only for agreement on pairs with one vector tangent to the submanifold. -/
theorem isContactFormAt_add_smul_sub_of_mextDeriv_eq_on {x : M} (hc : IsContactFormAt α₀.val x)
    (hval : α₁.val x = α₀.val x) {W : Submodule ℝ (TangentSpace I x)}
    (hWk : ∀ w ∈ W, w ∈ RoughForm.ker α₀.val x)
    (hW : ∀ v ∈ RoughForm.ker α₀.val x, (∀ w ∈ W, mextDeriv α₀.val x ![w, v] = 0) → v ∈ W)
    (hd : ∀ w ∈ W, ∀ v ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![w, v] = mextDeriv α₀.val x ![w, v]) (s : ℝ) :
    IsContactFormAt (α₀ + s • (α₁ - α₀)).val x := by
  have hval' : (α₀ + s • (α₁ - α₀)).val x = α₀.val x := by simp [hval]
  -- On `W × ker α₀ x`, the exterior derivative of the interpolation is that of `α₀`.
  have hdW (w : TangentSpace I x) (hw : w ∈ W) (v : TangentSpace I x)
      (hv : v ∈ RoughForm.ker α₀.val x) :
      mextDeriv (α₀ + s • (α₁ - α₀)).val x ![w, v] = mextDeriv α₀.val x ![w, v] := by
    rw [← mextDerivₗ_apply I 1 (α₀ + s • (α₁ - α₀)), map_add, map_smul, map_sub]
    simp [hd w hw v hv]
  have hswap (β : RoughForm I M ℝ 1) (v w : TangentSpace I x) :
      mextDeriv β x ![v, w] = -mextDeriv β x ![w, v] := by
    simpa using (mextDeriv β x).apply_vecCons_swap w v
  have hker {u : TangentSpace I x} :
      u ∈ RoughForm.ker (α₀ + s • (α₁ - α₀)).val x ↔ u ∈ RoughForm.ker α₀.val x := by
    rw [RoughForm.mem_ker, RoughForm.mem_ker, hval']
  refine ⟨hval'.symm ▸ hc.ne_zero, fun v hv hvw ↦ ?_⟩
  rw [hker] at hv
  -- A vector of `ker α₀ x` in the kernel of the interpolated form is orthogonal to `W`, so it
  -- lies in `W`; there its pairings are those of `dα₀ x`, so it vanishes.
  have hvW : v ∈ W := hW v hv fun w hw ↦ by
    rw [← hdW w hw v hv, hswap, hvw w (hker.2 (hWk w hw)), neg_zero]
  exact hc.nondegenerate v hv fun w hw ↦ by rw [← hdW v hvW w hw, hvw w (hker.2 hw)]

/-- **Interpolations of forms agreeing to first order at a contact point are contact there.** If
`α₀` is contact at `x`, `α₁ x = α₀ x`, and `dα₁ x` agrees with `dα₀ x` on the hyperplane
`ker α₀ x`, then every form `α₀ + s (α₁ - α₀)` is contact at `x`. -/
theorem isContactFormAt_add_smul_sub {x : M} (hc : IsContactFormAt α₀.val x)
    (hval : α₁.val x = α₀.val x)
    (hd : ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) (s : ℝ) :
    IsContactFormAt (α₀ + s • (α₁ - α₀)).val x :=
  isContactFormAt_add_smul_sub_of_mextDeriv_eq_on (W := RoughForm.ker α₀.val x) hc hval
    (fun _ h ↦ h) (fun _ hv _ ↦ hv) hd s

/-- On the segment `[0, 1]`, the factor `1 + s (c - 1) = (1 - s) + s c` by which the interpolation
of `α₀` and `c α₀` rescales `α₀` is positive when `c` is. -/
private theorem one_add_mul_sub_one_pos {s c : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (hc : 0 < c) :
    0 < 1 + s * (c - 1) := by
  rcases hs₁.lt_or_eq with hs | rfl
  · nlinarith [mul_nonneg hs₀ hc.le]
  · linarith

/-- At a point where `α₁ = c α₀`, the interpolation `α₀ + s (α₁ - α₀)` is
`(1 + s (c - 1)) α₀`. -/
private theorem add_smul_sub_apply_of_eq_smul {x : M} {c : ℝ} (hval : α₁.val x = c • α₀.val x)
    (s : ℝ) : (α₀ + s • (α₁ - α₀)).val x = (1 + s * (c - 1)) • α₀.val x := by
  simp only [Submodule.coe_add, SetLike.val_smul, AddSubgroupClass.coe_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, hval]
  module

/-- **Interpolations of forms agreeing to first order up to a factor are contact.** If `α₀` is
contact at `x`, `α₁ x = c α₀ x`, and `dα₁ x = c dα₀ x` on the hyperplane `ker α₀ x`, then the form
`α₀ + s (α₁ - α₀)` is contact at `x` whenever `1 + s (c - 1) ≠ 0`; for `c > 0` this holds for every
`s ∈ [0, 1]`. -/
theorem isContactFormAt_add_smul_sub_of_eq_smul {x : M} {c s : ℝ} (hc : IsContactFormAt α₀.val x)
    (hval : α₁.val x = c • α₀.val x)
    (hd : ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = c * mextDeriv α₀.val x ![v, w])
    (hs : 1 + s * (c - 1) ≠ 0) :
    IsContactFormAt (α₀ + s • (α₁ - α₀)).val x := by
  -- At `x` the interpolated form is `(1 + s (c - 1)) α₀`, to first order on `ker α₀ x`.
  refine (isContactFormAt_congr_smul hs (add_smul_sub_apply_of_eq_smul hval s)
    fun v hv w hw ↦ ?_).2 hc
  rw [← mextDerivₗ_apply I 1 (α₀ + s • (α₁ - α₀)), map_add, map_smul, map_sub]
  simp [hd v hv w hw]
  ring

variable [FiniteDimensional ℝ E]

/-- **The interpolation is contact near a set where it is contact.** If every interpolation
`α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, is contact at the points of `K`, then there is an open
neighbourhood of `K` on which all of them are contact. The set `K` need not be compact. -/
theorem exists_isOpen_forall_isContactFormAt_add_smul_sub_of_isContactFormAt {K : Set M}
    (hcK : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + s • (α₁ - α₀)).val x) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1,
      IsContactFormAt (α₀ + s • (α₁ - α₀)).val x := by
  -- The interpolations are contact on an open set `O ⊆ ℝ × M`: the contact points of the slices
  -- of the family `s ↦ α₀ + s (α₁ - α₀)`.
  set O := {p : ℝ × M | IsContactFormAt (α₀ + p.1 • (α₁ - α₀)).val p.2}
  have hO : IsOpen O := by
    simpa only [mpullback_prodMk_lineMapFamily, id] using
      isOpen_setOf_isContactFormAt_mpullback_prodMk (lineMapFamily α₀ α₁ contDiff_id)
  -- Since `[0, 1]` is compact, the points `x` with `[0, 1] × {x} ⊆ O` form an open set.
  exact ⟨{x | ∀ s ∈ Icc (0 : ℝ) 1, (s, x) ∈ O},
    isOpen_iff_mem_nhds.2 fun x hx ↦ isCompact_Icc.eventually_forall_of_forall_eventually
      fun s hs ↦ (hO.preimage continuous_swap).mem_nhds (hx s hs), hcK, fun _ hx ↦ hx⟩

/-- **The interpolation is contact near the set of first-order agreement up to a factor.** Let
`α₀` be contact at every point of `K`, and let `α₁ = c α₀` at the points of `K`, with `dα₁ = c dα₀`
on the hyperplanes `ker α₀`, for a function `c` positive on `K`. Then there is an open neighbourhood
of `K` on which every interpolation `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, is contact. The set `K` need
not be compact. -/
theorem exists_isOpen_forall_isContactFormAt_add_smul_sub_of_eq_smul {K : Set M} {c : M → ℝ}
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hc0 : ∀ x ∈ K, 0 < c x)
    (hval : ∀ x ∈ K, α₁.val x = c x • α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = c x * mextDeriv α₀.val x ![v, w]) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1,
      IsContactFormAt (α₀ + s • (α₁ - α₀)).val x :=
  exists_isOpen_forall_isContactFormAt_add_smul_sub_of_isContactFormAt fun x hx _ hs ↦
    isContactFormAt_add_smul_sub_of_eq_smul (hc x hx) (hval x hx) (hd x hx)
      (one_add_mul_sub_one_pos hs.1 hs.2 (hc0 x hx)).ne'

/-- **The interpolation is contact near the set of first-order agreement.** Let `α₀` be contact at
every point of `K`, and let `α₁` agree with `α₀` at the points of `K`, with `dα₁` agreeing with
`dα₀` on the hyperplanes `ker α₀`. Then there is an open neighbourhood of `K` on which every
interpolation `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, is contact. The set `K` need not be compact. -/
theorem exists_isOpen_forall_isContactFormAt_add_smul_sub {K : Set M}
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1,
      IsContactFormAt (α₀ + s • (α₁ - α₀)).val x :=
  exists_isOpen_forall_isContactFormAt_add_smul_sub_of_eq_smul (c := fun _ ↦ 1) hc
    (fun _ _ ↦ one_pos) (fun x hx ↦ by rw [hval x hx, one_smul]) fun x hx v hv w hw ↦ by
      rw [hd x hx v hv w hw, one_mul]

/-! ### Relative Gray stability for two contact forms -/

variable [I.Boundaryless] [T2Space M]

/-- **Relative Gray stability along a segment of contact forms.** Let every interpolation
`α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, be a contact form, and let `α₁` be a multiple of `α₀` at the
points of a set `K`; the multiple is then positive, as the segment never passes through zero. Then
there is a smooth partial diffeomorphism `φ` of `M`, whose source and target are open
neighbourhoods of `K`, which fixes every point of `K` and pulls `α₁` back to a positive multiple of
`α₀` on its source. Neither `K` nor `M` need be compact. -/
theorem exists_partialDiffeomorph_mpullback_eq_smul_of_forall_isContactFormAt {K : Set M}
    (hc : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + s • (α₁ - α₀)).val x)
    (hval : ∀ x ∈ K, ∃ c : ℝ, α₁.val x = c • α₀.val x) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, ∃ g : ℝ, 0 < g ∧ TauCeti.mpullback I I φ α₁.val x = g • α₀.val x := by
  -- The segment, reparametrized by the smooth step function, is a smooth family of contact forms.
  have hcα (t : ℝ) : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤)))).IsContactForm := by
    rw [mpullback_prodMk_lineMapFamily, isContactForm_iff_forall_isContactFormAt]
    exact fun x ↦ hc x _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- Along `K`, every form of the segment is a nonzero multiple of `α₀`, so its kernel does not
  -- move.
  have hK (x : M) (hx : x ∈ K) (u : ℝ) :
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id)
        (lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤)))).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id)
        (lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤)))).kerDistribution x := by
    obtain ⟨c, hcx⟩ := hval x hx
    have hu := (hc x _ ⟨Real.smoothTransition.nonneg u, Real.smoothTransition.le_one u⟩).ne_zero
    rw [add_smul_sub_apply_of_eq_smul hcx] at hu
    ext v
    rw [mpullback_prodMk_lineMapFamily, mpullback_prodMk_lineMapFamily, mem_kerDistribution,
      mem_kerDistribution, add_smul_sub_apply_of_eq_smul hcx, add_smul_sub_apply_of_eq_smul hcx,
      Real.smoothTransition.zero, zero_mul, add_zero, one_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_zero, or_iff_right (left_ne_zero_of_smul hu)]
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ := exists_partialDiffeomorph_mpullback_eq_smul hcα hK 0 1
  refine ⟨φ, hsrc, htgt, hfix, fun x hx ↦ ?_⟩
  simpa [Real.smoothTransition.one, Real.smoothTransition.zero] using hφ x hx

/-- **Relative Gray stability for contact forms agreeing to first order up to a factor.** Let `α₀`
be contact at every point of a set `K`, and let `α₁ = c α₀` at the points of `K`, with `dα₁ = c dα₀`
on the hyperplanes `ker α₀`, for a function `c` positive on `K`. Then there is a smooth partial
diffeomorphism `φ` of `M`, whose source and target are open neighbourhoods of `K`, which fixes every
point of `K` and pulls `α₁` back to a positive multiple of `α₀` on its source. Neither `K` nor `M`
need be compact. Only `α₀` is assumed contact, and only at the points of `K`. -/
theorem exists_partialDiffeomorph_mpullback_eq_smul_of_eq_smul {K : Set M} {c : M → ℝ}
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hc0 : ∀ x ∈ K, 0 < c x)
    (hval : ∀ x ∈ K, α₁.val x = c x • α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = c x * mextDeriv α₀.val x ![v, w]) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, ∃ g : ℝ, 0 < g ∧ TauCeti.mpullback I I φ α₁.val x = g • α₀.val x := by
  -- Restrict both forms to an open neighbourhood `W` of `K` on which the segment is contact.
  obtain ⟨N, hN, hKN, hcN⟩ :=
    exists_isOpen_forall_isContactFormAt_add_smul_sub_of_eq_smul hc hc0 hval hd
  set W : TopologicalSpace.Opens M := ⟨N, hN⟩
  set res : SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I W ℝ 1 :=
    mpullback (Subtype.val : W → M) contMDiff_subtypeVal
  have hcW (y : W) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IsContactFormAt (res α₀ + s • (res α₁ - res α₀)).val y := by
    rw [← map_sub, ← map_smul, ← map_add]
    exact (isContactFormAt_mpullback_subtype_val_iff _ y).2 (hcN y y.property s hs)
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ :=
    exists_partialDiffeomorph_mpullback_eq_smul_of_forall_isContactFormAt (K := Subtype.val ⁻¹' K)
      hcW fun y hy ↦ ⟨c y, (coe_mpullback_subtype_val_apply α₁ y).trans ((hval y hy).trans
          (congrArg (c y • ·) (coe_mpullback_subtype_val_apply α₀ y).symm))⟩
  -- Read `φ` in `M`.
  obtain ⟨Φ, hsrcΦ, htgtΦ, hfixΦ, hΦ⟩ :=
    exists_partialDiffeomorph_mpullback_apply_eq_of_opens (by simp) hKN φ hsrc htgt hfix
  refine ⟨Φ, hsrcΦ, htgtΦ, hfixΦ, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl, hΦy⟩ := hΦ x hx
  obtain ⟨g, hg, hφy⟩ := hφ y hy
  refine ⟨g, hg, (hΦy α₁.val).trans ?_⟩
  rw [coe_mpullback, coe_mpullback] at hφy
  exact hφy.trans (congrArg (g • ·) (mpullback_subtype_val_apply α₀.val y))

/-- **Relative Gray stability for contact forms agreeing to first order along a set.** Let `α₀` be
contact at every point of a set `K`, and let `α₁` agree with `α₀` at the points of `K`, with `dα₁`
agreeing with `dα₀` on the hyperplanes `ker α₀`. Then there is a smooth partial diffeomorphism `φ`
of `M`, whose source and target are open neighbourhoods of `K`, which fixes every point of `K` and
pulls `α₁` back to a positive multiple of `α₀` on its source. Neither `K` nor `M` need be compact.
Only `α₀` is assumed contact, and only at the points of `K`. -/
theorem exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq {K : Set M}
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, ∃ g : ℝ, 0 < g ∧ TauCeti.mpullback I I φ α₁.val x = g • α₀.val x :=
  exists_partialDiffeomorph_mpullback_eq_smul_of_eq_smul (c := fun _ ↦ 1) hc (fun _ _ ↦ one_pos)
    (fun x hx ↦ by rw [hval x hx, one_smul]) fun x hx v hv w hw ↦ by
      rw [hd x hx v hv w hw, one_mul]

end TauCeti.SmoothForm
