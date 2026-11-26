/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Forms
public import TauCeti.Analysis.Complex.Wirtinger.Potential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Complex.PowerSeries.Polydisc
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Topology.MetricSpace.Pseudo.Pi

/-!
# The `bar∂`-Poincaré lemma on polydiscs

On the coordinate space `ι → ℂ` of a finite index type `ι`, write
`∂f/∂(conj z_j) = conjWirtingerDeriv f z (Pi.single j 1)` for the conjugate Wirtinger derivative
in the `j`-th coordinate. For a linear order on `ι`, a `(0,q)`-form `∑_J f_J d(conj z)_J` with
coefficients in a complex Banach space `F` is recorded by its coefficients
`f : Finset ι → (ι → ℂ) → F`, and `TauCeti.delBarCoeff f` is the family of coefficients of its
`bar∂` (see `TauCeti.Analysis.Complex.Wirtinger.Forms`).

This file proves the Dolbeault–Grothendieck lemma for such forms in coordinates: for `q ≥ 1`, a
smooth `bar∂`-closed `(0,q)`-form on a product domain `∏ U_i` of open sets `U_i ⊆ ℂ` is
`bar∂`-exact near every compact product `∏ K_i` with `K_i ⊆ U_i`, and on a polydisc it is
`bar∂`-exact on the whole polydisc. That is, some `(0,q-1)`-form `u`, smooth there, satisfies
`bar∂ u = f` there. Taking coefficients
in `Finset ι → F` gives the same statement for `(p,q)`-forms, whose `bar∂` is `(-1)^p` times the
`bar∂` of the corresponding `(0,q)`-form with these vector coefficients. For `q = 1` the lemma
reads: a `(0,1)`-form `∑ j, f_j d(conj z_j)` with `∂f_j/∂(conj z_i) = ∂f_i/∂(conj z_j)` for all
`i, j` has a smooth `u` with `∂u/∂(conj z_j) = f_j`; this form of it needs no order on `ι`.

The proof eliminates one conjugate variable at a time, as in Hörmander and Griffiths–Harris. The
elimination step
`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_single_eventually_eq_of_pi` solves
`∂v/∂(conj z_k) = g` in one coordinate `z_k`. If `g` is holomorphic in a set `T` of other
coordinates, the solution `v` can be chosen holomorphic in those coordinates as well; it is
`Cⁿ`, like `g`. This is the one-variable solver
`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_holomorphic_param`
with the coordinates outside `{k} ∪ T` as smooth parameters and those in `T` as holomorphic
parameters. If `f` only involves `d(conj z_j)` for `j` in `insert k S`, write
`f = d(conj z_k) ∧ g + h` with `g` and `h` only involving the `d(conj z_j)`, `j ∈ S`. Closedness
of `f` makes the coefficients of `g` holomorphic in the coordinates outside `insert k S`, so the
elimination step gives a `(0,q-1)`-form `γ` with `∂γ_J/∂(conj z_k) = g_J`, holomorphic in those
coordinates; then `f - bar∂ γ` is closed and only involves the `d(conj z_j)`, `j ∈ S`.

On a polydisc, local solutions on an exhaustion by smaller concentric polydiscs are corrected so
that they converge on the whole polydisc, as in Hörmander's Theorem 2.3.3. For `(0,1)`-forms the
corrections are partial sums of multivariate Cauchy expansions of the holomorphic differences of
consecutive solutions (`DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi`); in higher
degree they are `bar∂` of local primitives of the `bar∂`-closed differences, and the corrected
solutions stabilize.

## Main results

* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_single_eventually_eq_of_pi`: the
  elimination step, solving `∂v/∂(conj z_k) = g` and keeping holomorphy in the coordinates where
  `g` is holomorphic.
* `TauCeti.exists_contDiffAt_delBarCoeff_eventually_eq_of_pi`: a smooth `bar∂`-closed
  `(0,q+1)`-form on a product of open subsets of `ℂ` is `bar∂`-exact near every compact product
  inside it.
* `TauCeti.exists_contDiffOn_delBarCoeff_eq_of_polydisc`: a smooth `bar∂`-closed `(0,q+1)`-form
  on a polydisc is `bar∂`-exact on the whole polydisc.
* `TauCeti.exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi`,
  `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_single_eq_of_polydisc`: the case of
  `(0,1)`-forms `∑ j, f_j d(conj z_j)`, for any finite index type.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 2.3.3.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §2
  (the `bar∂`-Poincaré lemma in several variables).
-/

public section

open Complex Filter Set Topology
open scoped ContDiff Finset

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

section Elimination

variable {ι : Type*} [DecidableEq ι]

/-! ### Coordinate blocks -/

section Blocks

variable (k : ι) (T : Finset ι)

/-- The point whose `k`-th coordinate is `w`, whose coordinates in `T` are those of `x.2` and
whose remaining coordinates are those of `x.1`. -/
private def glue (x : (ι → ℂ) × (ι → ℂ)) (w : ℂ) : ι → ℂ :=
  Function.update (T.piecewise x.2 x.1) k w

/-- The parameters of a point: its coordinates outside `{k} ∪ T`, and its coordinates in `T`. -/
private def split (z : ι → ℂ) : (ι → ℂ) × (ι → ℂ) :=
  (T.piecewise 0 (Function.update z k 0), T.piecewise z 0)

private theorem glue_split (z : ι → ℂ) : glue k T (split k T z) (z k) = z := by
  ext i
  by_cases hik : i = k
  · subst hik
    simp [glue]
  · by_cases hiT : i ∈ T <;> simp [glue, split, hik, hiT]

variable {k T}

/-- Moving along the `k`-th coordinate does not change the parameters. -/
private theorem split_add_smul_single_self (hk : k ∉ T) (z : ι → ℂ) (t : ℂ) :
    split k T (z + t • Pi.single k 1) = split k T z := by
  ext i
  · by_cases hiT : i ∈ T
    · simp [split, hiT]
    · by_cases hik : i = k
      · subst hik
        simp [split, hiT]
      · simp [split, hiT, hik]
  · by_cases hiT : i ∈ T
    · simp [split, hiT, show i ≠ k from fun h ↦ hk (h ▸ hiT)]
    · simp [split, hiT]

/-- Moving along a coordinate in `T` moves the holomorphic parameter only. -/
private theorem split_add_smul_single_of_mem (hk : k ∉ T) {j : ι} (hj : j ∈ T) (z : ι → ℂ)
    (t : ℂ) :
    split k T (z + t • Pi.single j 1) =
      ((split k T z).1, (split k T z).2 + t • Pi.single j 1) := by
  ext i
  · by_cases hiT : i ∈ T
    · simp [split, hiT]
    · by_cases hik : i = k
      · subst hik
        simp [split, hiT]
      · simp [split, hiT, hik, show i ≠ j from fun h ↦ hiT (h ▸ hj)]
  · by_cases hiT : i ∈ T
    · simp [split, hiT]
    · simp [split, hiT, show i ≠ j from fun h ↦ hiT (h ▸ hj)]

/-- Moving the holomorphic parameter moves the glued point along the coordinates in `T`. -/
private theorem glue_add_smul (hk : k ∉ T) (x : (ι → ℂ) × (ι → ℂ)) (w t : ℂ)
    (v : ι → ℂ) :
    glue k T (x.1, x.2 + t • v) w = glue k T x w + t • T.piecewise v 0 := by
  ext i
  by_cases hik : i = k
  · subst hik
    simp [glue, hk]
  · by_cases hiT : i ∈ T <;> simp [glue, hik, hiT]

variable [Fintype ι]

private theorem contDiff_glue (k : ι) (T : Finset ι) :
    ContDiff ℝ ⊤ fun y : ((ι → ℂ) × (ι → ℂ)) × ℂ ↦ glue k T y.1 y.2 := by
  refine contDiff_pi' fun i ↦ ?_
  by_cases hik : i = k
  · subst hik
    simpa [glue] using contDiff_snd
  · by_cases hiT : i ∈ T <;> simp only [glue, Function.update_of_ne hik, Finset.piecewise, hiT,
      ite_true, ite_false] <;> fun_prop

private theorem contDiff_split (k : ι) (T : Finset ι) :
    ContDiff ℝ ⊤ fun z : ι → ℂ ↦ (split k T z, z k) := by
  refine ((contDiff_pi' fun i ↦ ?_).prodMk (contDiff_pi' fun i ↦ ?_)).prodMk (by fun_prop)
  · by_cases hiT : i ∈ T
    · simpa [split, hiT] using contDiff_const
    · by_cases hik : i = k
      · subst hik
        simpa [split, hiT] using contDiff_const
      · simp only [Finset.piecewise, hiT, ite_false, Function.update_of_ne hik]
        fun_prop
  · by_cases hiT : i ∈ T
    · simp only [Finset.piecewise, hiT, ite_true]
      fun_prop
    · simpa [split, hiT] using contDiff_const

/-- An antilinear map vanishing on the coordinate vectors indexed by `T` vanishes on every vector
supported in `T`. -/
private theorem conjWirtingerDeriv_piecewise_eq_zero {g : (ι → ℂ) → F} {z : ι → ℂ}
    (h : ∀ j ∈ T, conjWirtingerDeriv g z (Pi.single j 1) = 0) (v : ι → ℂ) :
    conjWirtingerDeriv g z (T.piecewise v 0) = 0 := by
  have hv : T.piecewise v 0 = ∑ j ∈ T, v j • Pi.single j 1 := by
    ext i
    by_cases hiT : i ∈ T <;> simp [hiT, Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  exact Finset.sum_eq_zero fun j hj ↦ by simp [h j hj]

/-- A map holomorphic in each coordinate of `T` at a glued point is holomorphic there in the
holomorphic parameter. -/
private theorem differentiableAt_glue (hk : k ∉ T) {g : (ι → ℂ) → F}
    {x : (ι → ℂ) × (ι → ℂ)} {w : ℂ} (hg : DifferentiableAt ℝ g (glue k T x w))
    (hgT : ∀ j ∈ T, conjWirtingerDeriv g (glue k T x w) (Pi.single j 1) = 0) :
    DifferentiableAt ℂ (fun q ↦ g (glue k T (x.1, q) w)) x.2 := by
  have hι : ContDiff ℝ ⊤ fun q : ι → ℂ ↦ glue k T (x.1, q) w :=
    (contDiff_glue k T).comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hd : DifferentiableAt ℝ (fun q ↦ g (glue k T (x.1, q) w)) x.2 :=
    hg.comp x.2 (hι.differentiable (by simp) x.2)
  refine (differentiableAt_iff_conjWirtingerDeriv_eq_zero hd).2
    (ContinuousLinearMap.ext fun v ↦ ?_)
  rw [conjWirtingerDeriv_apply_eq_conjWirtingerDeriv_line hd]
  simp only [glue_add_smul hk]
  rw [← conjWirtingerDeriv_apply_eq_conjWirtingerDeriv_line hg,
    conjWirtingerDeriv_piecewise_eq_zero hgT, zero_apply]

/-- A map holomorphic in the holomorphic parameter is holomorphic in each coordinate of `T`. -/
private theorem conjWirtingerDeriv_comp_split_single_of_mem (hk : k ∉ T)
    {u : (ι → ℂ) × (ι → ℂ) → ℂ → F} {z : ι → ℂ}
    (hu : DifferentiableAt ℝ (fun y : ((ι → ℂ) × (ι → ℂ)) × ℂ ↦ u y.1 y.2) (split k T z, z k))
    (hq : DifferentiableAt ℂ (fun q ↦ u ((split k T z).1, q) (z k)) (split k T z).2) {j : ι}
    (hj : j ∈ T) :
    conjWirtingerDeriv (fun z ↦ u (split k T z) (z k)) z (Pi.single j 1) = 0 := by
  have hjk : j ≠ k := fun h ↦ hk (h ▸ hj)
  rw [conjWirtingerDeriv_apply_eq_conjWirtingerDeriv_line
    (hu.fun_comp' z ((contDiff_split k T).differentiable (by simp) z))]
  simp only [split_add_smul_single_of_mem hk hj, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_of_ne hjk.symm, smul_zero, add_zero]
  have hline : DifferentiableAt ℂ (fun t : ℂ ↦ (split k T z).2 + t • Pi.single j 1) 0 := by
    fun_prop
  have hq' : DifferentiableAt ℂ (fun q ↦ u ((split k T z).1, q) (z k))
      ((split k T z).2 + (0 : ℂ) • Pi.single j 1) := by
    simpa using hq
  have hcomp : DifferentiableAt ℂ
      (fun t : ℂ ↦ u ((split k T z).1, (split k T z).2 + t • Pi.single j 1) (z k)) 0 :=
    hq'.fun_comp' (0 : ℂ) hline
  simp [hcomp.conjWirtingerDeriv_eq_zero]

/-- Along the `k`-th coordinate, the conjugate Wirtinger derivative is the one-variable conjugate
Wirtinger derivative in the last argument. -/
private theorem conjWirtingerDeriv_comp_split_single_self (hk : k ∉ T)
    {u : (ι → ℂ) × (ι → ℂ) → ℂ → F} {z : ι → ℂ}
    (hu : DifferentiableAt ℝ (fun y : ((ι → ℂ) × (ι → ℂ)) × ℂ ↦ u y.1 y.2) (split k T z, z k)) :
    conjWirtingerDeriv (fun z ↦ u (split k T z) (z k)) z (Pi.single k 1) =
      conjWirtingerDeriv (u (split k T z)) (z k) 1 := by
  have hd : DifferentiableAt ℝ (u (split k T z)) (z k) :=
    hu.fun_comp' (z k) (differentiableAt_const _ |>.prodMk differentiableAt_id)
  rw [conjWirtingerDeriv_apply_eq_conjWirtingerDeriv_line
    (hu.fun_comp' z ((contDiff_split k T).differentiable (by simp) z))]
  simp only [split_add_smul_single_self hk, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
  rw [← conjWirtingerDeriv_apply_eq_conjWirtingerDeriv_line hd]

end Blocks

/-! ### Elimination of one conjugate variable -/

variable [Fintype ι] [CompleteSpace F]

/-- **Elimination of one conjugate variable.** Let `g` be `Cⁿ`, `1 ≤ n`, on a product `∏ U_i` of
open subsets of `ℂ`, and holomorphic there in each coordinate of a set `T` not containing `k`.
For every compact `L ⊆ U_k` there is a `Cⁿ` map `v` on `∏ U_i`, holomorphic there in each
coordinate of `T`, with `∂v/∂(conj z_k) = g` wherever `z_k` lies near `L`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_single_eventually_eq_of_pi {n : ℕ∞}
    (hn : 1 ≤ n) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) {k : ι} {T : Finset ι} (hk : k ∉ T)
    {L : Set ℂ} (hL : IsCompact L) (hLU : L ⊆ U k) {g : (ι → ℂ) → F}
    (hg : ContDiffOn ℝ n g (univ.pi U))
    (hgT : ∀ z ∈ univ.pi U, ∀ j ∈ T, conjWirtingerDeriv g z (Pi.single j 1) = 0) :
    ∃ v : (ι → ℂ) → F, ContDiffOn ℝ n v (univ.pi U) ∧
      (∀ z ∈ univ.pi U, ∀ j ∈ T, conjWirtingerDeriv v z (Pi.single j 1) = 0) ∧
      ∀ᶠ w in 𝓝ˢ L, ∀ z ∈ univ.pi U, z k = w → conjWirtingerDeriv v z (Pi.single k 1) = g z := by
  have hpi : IsOpen (univ.pi U) := isOpen_set_pi finite_univ fun i _ ↦ hU i
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le hn).ne'
  -- The parameter domain: points whose coordinates other than the `k`-th lie in the `U_i`.
  set s : Set ((ι → ℂ) × (ι → ℂ)) :=
    (fun x ↦ T.piecewise x.2 x.1) ⁻¹' univ.pi (Function.update U k univ)
  have hs : IsOpen s := by
    refine IsOpen.preimage ?_ (isOpen_set_pi finite_univ fun i _ ↦ ?_)
    · exact continuous_pi fun i ↦ by
        by_cases hiT : i ∈ T <;> simp only [Finset.piecewise, hiT, ite_true, ite_false] <;>
          fun_prop
    · by_cases hik : i = k
      · subst hik
        simp
      · simpa [hik] using hU i
  have hglue {x : (ι → ℂ) × (ι → ℂ)} {w : ℂ} (hx : x ∈ s) (hw : w ∈ U k) :
      glue k T x w ∈ univ.pi U := fun i _ ↦ by
    by_cases hik : i = k
    · subst hik
      simpa [glue] using hw
    · simpa [glue, hik] using hx i (mem_univ i)
  have hsplit {z : ι → ℂ} (hz : z ∈ univ.pi U) : split k T z ∈ s := fun i _ ↦ by
    by_cases hik : i = k
    · subst hik
      simp
    · by_cases hiT : i ∈ T <;> simpa [split, hik, hiT] using hz i (mem_univ i)
  have hgd {z : ι → ℂ} (hz : z ∈ univ.pi U) : DifferentiableAt ℝ g z :=
    (hg.contDiffAt (hpi.mem_nhds hz)).differentiableAt hn'
  -- The family solved by the one-variable solver is holomorphic in the parameters from `T`.
  have hf : ContDiffOn ℝ n (fun y : ((ι → ℂ) × (ι → ℂ)) × ℂ ↦ g (glue k T y.1 y.2))
      (s ×ˢ U k) :=
    hg.comp ((contDiff_glue k T).of_le le_top).contDiffOn fun y hy ↦ hglue hy.1 hy.2
  have hfq : ∀ x ∈ s, ∀ w ∈ U k, DifferentiableAt ℂ (fun q ↦ g (glue k T (x.1, q) w)) x.2 :=
    fun x hx w hw ↦ differentiableAt_glue hk (hgd (hglue hx hw)) (hgT _ (hglue hx hw))
  obtain ⟨u, hu, hsol, hhol⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_holomorphic_param
      (f := fun x w ↦ g (glue k T x w)) hn hs (hU k) hL hLU hf hfq
  have hsu : IsOpen (s ×ˢ (univ : Set ℂ)) := hs.prod isOpen_univ
  have hud {x : (ι → ℂ) × (ι → ℂ)} (hx : x ∈ s) (w : ℂ) :
      DifferentiableAt ℝ (fun y : ((ι → ℂ) × (ι → ℂ)) × ℂ ↦ u y.1 y.2) (x, w) :=
    (hu.contDiffAt (hsu.mem_nhds ⟨hx, mem_univ w⟩)).differentiableAt hn'
  -- The solution in the `k`-th coordinate, with the other coordinates as parameters.
  refine ⟨fun z ↦ u (split k T z) (z k), ?_, ?_, ?_⟩
  · exact hu.comp ((contDiff_split k T).of_le le_top).contDiffOn
      fun z hz ↦ ⟨hsplit hz, mem_univ _⟩
  · exact fun z hz j hj ↦ conjWirtingerDeriv_comp_split_single_of_mem hk (hud (hsplit hz) (z k))
      (hhol _ (hsplit hz) _) hj
  · filter_upwards [hsol] with w hw z hz hzw
    subst hzw
    rw [conjWirtingerDeriv_comp_split_single_self hk (hud (hsplit hz) (z k)), hw _ (hsplit hz),
      glue_split]

end Elimination

/-! ### The `bar∂`-Poincaré lemma for `(0,q)`-forms -/

section Forms

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- For `k ∉ S`, let `f` be a `bar∂`-closed `(0,q+1)`-form on an open set whose coefficients vanish
unless their index set lies in `insert k S`. For `J ⊆ S` the coefficient of `d(conj z)_{insert k J}`
is holomorphic in the coordinates outside `insert k S`. -/
private theorem conjWirtingerDeriv_insert_eq_zero_of_delBarCoeff_eq_zero {q : ℕ}
    {U : Set (ι → ℂ)} (hU : IsOpen U) {f : Finset ι → (ι → ℂ) → F}
    (hclosed : ∀ z ∈ U, ∀ I, #I = q + 2 → delBarCoeff f I z = 0) {k : ι} {S : Finset ι}
    (hkS : k ∉ S) (hS : ∀ I, #I = q + 1 → ¬I ⊆ insert k S → ∀ z ∈ U, f I z = 0)
    {J : Finset ι} (hJS : J ⊆ S) (hJ : #J = q) {z : ι → ℂ} (hz : z ∈ U) {j : ι}
    (hj : j ∉ insert k S) :
    conjWirtingerDeriv (f (insert k J)) z (Pi.single j 1) = 0 := by
  have hkJ : k ∉ J := fun h ↦ hkS (hJS h)
  have hjJ : j ∉ insert k J := fun h ↦ hj (Finset.insert_subset_insert k hJS h)
  have hcard : #(insert j (insert k J)) = q + 2 := by
    rw [Finset.card_insert_of_notMem hjJ, Finset.card_insert_of_notMem hkJ, hJ]
  have h := hclosed z hz _ hcard
  rw [delBarCoeff_def, Finset.sum_eq_single j ?_ fun h ↦ absurd (Finset.mem_insert_self j _) h,
    Finset.erase_insert hjJ] at h
  · exact (smul_eq_zero.1 h).resolve_left (pow_ne_zero _ (by norm_num))
  · intro i hi hij
    -- The coefficient indexed by `insert j (insert k J) \ {i}` vanishes near `z`, since `j` lies
    -- in its index set.
    have hvan : f ((insert j (insert k J)).erase i) =ᶠ[𝓝 z] fun _ ↦ 0 := by
      refine eventually_of_mem (hU.mem_nhds hz) fun y hy ↦ hS _ ?_ (fun hsub ↦ ?_) y hy
      · rw [Finset.card_erase_of_mem hi, hcard]
        omega
      · exact hj (hsub (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_insert_self j _⟩))
    simp [hvan.conjWirtingerDeriv_eq]

/-- Let `k ∉ S`, and let `f` be a `(0,q+1)`-form whose coefficients at `z` vanish unless their index
set lies in `insert k S`. Let `v` be a `(0,q)`-form holomorphic at `z` in the coordinates outside
`insert k S` with `∂v_J/∂(conj z_k) = (-1)^#{i ∈ J | i < k} f_{insert k J}` at `z` for `J ⊆ S`.
Then the form `γ` obtained by keeping the coefficients of `v` indexed by subsets of `S` has
`(bar∂ γ)_I = f_I` at `z` for every `I` not contained in `S`. -/
private theorem delBarCoeff_ite_subset_eq {q : ℕ} {k : ι} {S : Finset ι}
    (hkS : k ∉ S) {f v : Finset ι → (ι → ℂ) → F} {z : ι → ℂ}
    (hv : ∀ J, ∀ j ∉ insert k S, conjWirtingerDeriv (v J) z (Pi.single j 1) = 0)
    (hvk : ∀ J ⊆ S, #J = q → conjWirtingerDeriv (v J) z (Pi.single k 1) =
      (-1 : ℂ) ^ #{i ∈ J | i < k} • f (insert k J) z)
    (hf : ∀ I, #I = q + 1 → ¬I ⊆ insert k S → f I z = 0) {I : Finset ι} (hI : #I = q + 1)
    (hIS : ¬I ⊆ S) :
    delBarCoeff (fun J ↦ if J ⊆ S then v J else 0) I z = f I z := by
  rw [delBarCoeff_def]
  by_cases hIk : I ⊆ insert k S
  · -- Only the term `j = k` survives, and it is `f_I`.
    have hk : k ∈ I := by_contra fun h ↦ hIS ((Finset.subset_insert_iff_of_notMem h).1 hIk)
    rw [Finset.sum_eq_single k ?_ (absurd hk)]
    · have hsub : I.erase k ⊆ S := Finset.subset_insert_iff.1 hIk
      have hfilt : {i ∈ I.erase k | i < k} = {i ∈ I | i < k} := by
        rw [Finset.filter_erase, Finset.erase_eq_of_notMem (s := {i ∈ I | i < k}) (by simp)]
      have hcard : #(I.erase k) = q := by
        rw [Finset.card_erase_of_mem hk, hI]
        omega
      simp only [hsub, ite_true]
      rw [hvk _ hsub hcard, Finset.insert_erase hk, hfilt]
      simp [smul_smul, ← mul_pow]
    · intro j _ hjk
      have hsub : ¬I.erase j ⊆ S := fun h ↦ hkS (h (Finset.mem_erase.2 ⟨Ne.symm hjk, hk⟩))
      simp [hsub]
  · -- Every term vanishes, as does `f_I`.
    rw [hf I hI hIk]
    obtain ⟨j₀, hj₀I, hj₀⟩ := Finset.not_subset.1 hIk
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hsub : I.erase j ⊆ S
    · obtain rfl : j = j₀ := by_contra fun h ↦
        hj₀ (Finset.mem_insert_of_mem (hsub (Finset.mem_erase.2 ⟨Ne.symm h, hj₀I⟩)))
      simp [hsub, hv _ _ hj₀]
    · simp [hsub]

variable [CompleteSpace F]

/-- Solve the conjugate `k`-derivative equation for a coefficient indexed by a `q`-element subset
of `S` of a closed form, preserving holomorphy outside `insert k S`. -/
private theorem exists_contDiffOn_delBarCoeff_insert_step {q : ℕ} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {f : Finset ι → (ι → ℂ) → F}
    (hf : ∀ I, #I = q + 1 → ContDiffOn ℝ ∞ (f I) (univ.pi U))
    (hclosed : ∀ z ∈ univ.pi U, ∀ I, #I = q + 2 → delBarCoeff f I z = 0)
    {k : ι} {S : Finset ι} (hkS : k ∉ S)
    (hS : ∀ I, #I = q + 1 → ¬I ⊆ insert k S → ∀ z ∈ univ.pi U, f I z = 0)
    {W : ι → Set ℂ} (hWc : IsCompact (closure (W k)))
    (hWU : ∀ i, closure (W i) ⊆ U i) (J : Finset ι) :
    ∃ v : (ι → ℂ) → F, ContDiffOn ℝ ∞ v (univ.pi U) ∧
      (∀ z ∈ univ.pi U, ∀ j ∉ insert k S, conjWirtingerDeriv v z (Pi.single j 1) = 0) ∧
      (J ⊆ S → #J = q → ∀ z ∈ univ.pi W, conjWirtingerDeriv v z (Pi.single k 1) =
        (-1 : ℂ) ^ #{i ∈ J | i < k} • f (insert k J) z) := by
  have hpi : IsOpen (univ.pi U) := isOpen_set_pi finite_univ fun i _ ↦ hU i
  have hWsub : univ.pi W ⊆ univ.pi U :=
    pi_mono fun i _ ↦ subset_closure.trans (hWU i)
  by_cases hJ : J ⊆ S ∧ #J = q
  · have hcard : #(insert k J) = q + 1 := by
      rw [Finset.card_insert_of_notMem fun h ↦ hkS (hJ.1 h), hJ.2]
    have hT : k ∉ (insert k S)ᶜ := by simp
    obtain ⟨v, hv, hvT, hvk⟩ :=
      exists_contDiffOn_conjWirtingerDeriv_apply_single_eventually_eq_of_pi le_top hU hT
        hWc (hWU k) (g := (-1 : ℂ) ^ #{i ∈ J | i < k} • f (insert k J))
        ((hf _ hcard).const_smul _)
        fun z hz j hj ↦ by
          rw [conjWirtingerDeriv_const_smul, _root_.smul_apply,
            conjWirtingerDeriv_insert_eq_zero_of_delBarCoeff_eq_zero hpi hclosed hkS hS
              hJ.1 hJ.2 hz (Finset.mem_compl.1 hj), smul_zero]
    refine ⟨v, hv, fun z hz j hj ↦ hvT z hz j (Finset.mem_compl.2 hj), fun _ _ z hz ↦ ?_⟩
    exact hvk.self_of_nhdsSet (z k) (subset_closure (hz k (mem_univ k))) z (hWsub hz) rfl
  · exact ⟨0, contDiffOn_const, fun z _ j _ ↦ by simp, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ hJ⟩

/-- The induction behind `TauCeti.exists_contDiffAt_delBarCoeff_eventually_eq_of_pi`, on the
finite set `S` of coordinates `j` such that `d(conj z_j)` may occur in the form. -/
private theorem exists_contDiffAt_delBarCoeff_eventually_eq_of_pi_of_eq_zero (q : ℕ)
    (S : Finset ι) :
    ∀ {U : ι → Set ℂ}, (∀ i, IsOpen (U i)) → ∀ {f : Finset ι → (ι → ℂ) → F},
      (∀ I, #I = q + 1 → ContDiffOn ℝ ∞ (f I) (univ.pi U)) →
      (∀ z ∈ univ.pi U, ∀ I, #I = q + 2 → delBarCoeff f I z = 0) →
      (∀ I, #I = q + 1 → ¬I ⊆ S → ∀ z ∈ univ.pi U, f I z = 0) →
      ∀ {K : ι → Set ℂ}, (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ U i) →
      ∃ u : Finset ι → (ι → ℂ) → F, ∀ᶠ z in 𝓝ˢ (univ.pi K),
        (∀ J, ContDiffAt ℝ ∞ (u J) z) ∧ ∀ I, #I = q + 1 → delBarCoeff u I z = f I z := by
  induction S using Finset.induction_on with
  | empty =>
    intro U hU f _ _ hS K _ hKU
    have hpi : IsOpen (univ.pi U) := isOpen_set_pi finite_univ fun i _ ↦ hU i
    refine ⟨0, ?_⟩
    filter_upwards [hpi.mem_nhdsSet.2 (pi_mono fun i _ ↦ hKU i)] with z hz
    refine ⟨fun _ ↦ contDiffAt_const, fun I hI ↦ ?_⟩
    have hI' : ¬I ⊆ ∅ := fun h ↦ by simp [Finset.subset_empty.1 h] at hI
    simp [hS I hI hI' z hz]
  | insert k S hkS ih =>
    intro U hU f hf hclosed hS K hK hKU
    have hpi : IsOpen (univ.pi U) := isOpen_set_pi finite_univ fun i _ ↦ hU i
    -- Shrink each `U_i` to an open `W_i ⊇ K_i` with compact closure inside `U_i`.
    choose W hWo hKW hWU hWc using fun i ↦
      exists_open_between_and_isCompact_closure (hK i) (hU i) (hKU i)
    have hWpi : IsOpen (univ.pi W) := isOpen_set_pi finite_univ fun i _ ↦ hWo i
    have hWsub : univ.pi W ⊆ univ.pi U :=
      pi_mono fun i _ ↦ subset_closure.trans (hWU i)
    -- Solve each coefficient equation, keeping holomorphy outside `insert k S`.
    choose v hvs hvT hvk using
      exists_contDiffOn_delBarCoeff_insert_step hU hf hclosed hkS hS (hWc k) hWU
    -- The `(0,q)`-form `γ` keeps the coefficients of `v` indexed by subsets of `S`.
    set γ : Finset ι → (ι → ℂ) → F := fun J ↦ if J ⊆ S then v J else 0 with hγ
    have hγa {z : ι → ℂ} (hz : z ∈ univ.pi U) (J : Finset ι) : ContDiffAt ℝ ∞ (γ J) z := by
      by_cases h : J ⊆ S
      · simpa [hγ, h] using (hvs J).contDiffAt (hpi.mem_nhds hz)
      · simp only [hγ, h, ite_false]
        exact contDiffAt_const
    have hdγ {z : ι → ℂ} (hz : z ∈ univ.pi U) (I : Finset ι) :
        ContDiffAt ℝ ∞ (delBarCoeff γ I) z :=
      contDiffAt_delBarCoeff (fun _ _ ↦ hγa hz _) (by simp)
    -- The remaining form `f - bar∂ γ` is `bar∂`-closed and only involves the coordinates in `S`.
    set f' : Finset ι → (ι → ℂ) → F := f - delBarCoeff γ with hf'
    have hf's : ∀ I, #I = q + 1 → ContDiffOn ℝ ∞ (f' I) (univ.pi W) := fun I hI ↦
      ((hf I hI).sub fun _ hz ↦ (hdγ hz I).contDiffWithinAt).mono hWsub
    have hclosed' : ∀ z ∈ univ.pi W, ∀ I, #I = q + 2 → delBarCoeff f' I z = 0 := by
      intro z hz I hI
      have hzU := hWsub hz
      rw [hf', delBarCoeff_sub (fun j hj ↦ ?_) (fun j _ ↦ (hdγ hzU _).differentiableAt (by simp)),
        hclosed z hzU I hI, delBarCoeff_delBarCoeff fun _ _ _ _ ↦ (hγa hzU _).of_le (by simp),
        sub_zero]
      have hcard : #(I.erase j) = q + 1 := by
        rw [Finset.card_erase_of_mem hj, hI]
        omega
      exact ((hf _ hcard).contDiffAt (hpi.mem_nhds hzU)).differentiableAt (by simp)
    have hS' : ∀ I, #I = q + 1 → ¬I ⊆ S → ∀ z ∈ univ.pi W, f' I z = 0 := by
      intro I hI hIS z hz
      rw [hf', Pi.sub_apply, Pi.sub_apply, sub_eq_zero, eq_comm]
      exact delBarCoeff_ite_subset_eq hkS (fun J j hj ↦ hvT J z (hWsub hz) j hj)
        (fun J hJS hJ ↦ hvk J hJS hJ z hz) (fun I hI hIk ↦ hS I hI hIk z (hWsub hz)) hI hIS
    obtain ⟨w, hw⟩ := ih hWo hf's hclosed' hS' hK hKW
    refine ⟨γ + w, ?_⟩
    filter_upwards [hw, hWpi.mem_nhdsSet.2 (pi_mono fun i _ ↦ hKW i)] with z hwz hz
    refine ⟨fun J ↦ (hγa (hWsub hz) J).add (hwz.1 J), fun I hI ↦ ?_⟩
    rw [delBarCoeff_add (fun _ _ ↦ (hγa (hWsub hz) _).differentiableAt (by simp))
      (fun _ _ ↦ (hwz.1 _).differentiableAt (by simp)), hwz.2 I hI, hf', Pi.sub_apply,
      Pi.sub_apply, add_sub_cancel]

/-- **The Dolbeault–Grothendieck lemma for `(0,q)`-forms on product domains.** Let
`f = ∑_I f_I d(conj z)_I` be a smooth `(0,q+1)`-form on a product `∏ U_i` of open subsets of `ℂ`,
with coefficients in a complex Banach space, which is `bar∂`-closed. Then near every compact
product `∏ K_i` with `K_i ⊆ U_i` it is `bar∂`-exact: some `(0,q)`-form `u`, smooth there,
satisfies `bar∂ u = f` there. -/
theorem exists_contDiffAt_delBarCoeff_eventually_eq_of_pi {q : ℕ} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {f : Finset ι → (ι → ℂ) → F}
    (hf : ∀ I, #I = q + 1 → ContDiffOn ℝ ∞ (f I) (univ.pi U))
    (hclosed : ∀ z ∈ univ.pi U, ∀ I, #I = q + 2 → delBarCoeff f I z = 0)
    {K : ι → Set ℂ} (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i) :
    ∃ u : Finset ι → (ι → ℂ) → F, ∀ᶠ z in 𝓝ˢ (univ.pi K),
      (∀ J, ContDiffAt ℝ ∞ (u J) z) ∧ ∀ I, #I = q + 1 → delBarCoeff u I z = f I z :=
  exists_contDiffAt_delBarCoeff_eventually_eq_of_pi_of_eq_zero q Finset.univ hU hf hclosed
    (fun I _ h ↦ absurd (Finset.subset_univ I) h) hK hKU

end Forms

/-! ### The `bar∂`-Poincaré lemma for `(0,1)`-forms -/

section OneForms

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [CompleteSpace F]

/-- **The `bar∂`-Poincaré lemma for `(0,1)`-forms on product domains.** Let
`f = ∑ j, f_j d(conj z_j)` be a smooth `(0,1)`-form on a product `∏ U_i` of open subsets of `ℂ`,
with coefficients in a complex Banach space, which is `bar∂`-closed:
`∂f_j/∂(conj z_i) = ∂f_i/∂(conj z_j)`. Then near every compact product `∏ K_i` with
`K_i ⊆ U_i` it is `bar∂`-exact: some `u`, smooth there, satisfies `∂u/∂(conj z_j) = f_j` for
every `j`. -/
theorem exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {f : ι → (ι → ℂ) → F} (hf : ∀ j, ContDiffOn ℝ ∞ (f j) (univ.pi U))
    (hclosed : ∀ z ∈ univ.pi U, ∀ i j,
      conjWirtingerDeriv (f j) z (Pi.single i 1) = conjWirtingerDeriv (f i) z (Pi.single j 1))
    {K : ι → Set ℂ} (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i) :
    ∃ u : (ι → ℂ) → F, ∀ᶠ z in 𝓝ˢ (univ.pi K),
      ContDiffAt ℝ ∞ u z ∧ ∀ j, conjWirtingerDeriv u z (Pi.single j 1) = f j z := by
  -- Order the coordinates, compatibly with the given decidable equality.
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain rfl : ‹DecidableEq ι› = LinearOrder.toDecidableEq := Subsingleton.elim _ _
  -- The form `f` as a `(0,1)`-form with coefficients indexed by singletons.
  obtain ⟨u, hu⟩ := exists_contDiffAt_delBarCoeff_eventually_eq_of_pi (q := 0) hU
    (f := fun I y ↦ ∑ j ∈ I, f j y) (fun I _ ↦ ContDiffOn.sum fun j _ ↦ hf j)
    (fun z hz I hI ↦ by
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hI
      rcases hab.lt_or_gt with h | h
      · simp only [delBarCoeff_pair _ h, Finset.sum_singleton, hclosed z hz a b, sub_self]
      · rw [Finset.pair_comm]
        simp only [delBarCoeff_pair _ h, Finset.sum_singleton, hclosed z hz b a, sub_self]) hK hKU
  refine ⟨u ∅, hu.mono fun z hz ↦ ⟨hz.1 ∅, fun j ↦ ?_⟩⟩
  simpa only [delBarCoeff_singleton, Finset.sum_singleton] using
    hz.2 {j} (Finset.card_singleton j)

end OneForms

/-! ### Whole polydiscs

The polydisc `∏ B(c_i, r_i)` is the increasing union of the concentric polydiscs `D_k` of
polyradius `r_i - 1 / (k + 1)`, each with closure inside the next. The local lemmas solve
`bar∂ u_k = f` on `D_k`, and the local solutions are corrected so that they converge on the whole
polydisc. For `(0,1)`-forms consecutive solutions differ by a holomorphic function on `D_k`,
which is approximated within `2⁻ᵏ` on `D_(k-1)` by an entire function, a partial sum of its
multivariate Cauchy expansion; subtracting these makes the solutions converge, and on each `D_m`
the limit is `u_m` plus a uniform limit of holomorphic functions. For `(0,q+2)`-forms the
difference of consecutive solutions is a `bar∂`-closed `(0,q+1)`-form on `D_k`, hence `bar∂` of a
`(0,q)`-form `g_k` near `D_(k-1)`; subtracting `bar∂ g_k`, which does not change `bar∂`, makes
consecutive solutions agree on `D_(k-1)`, so the solutions stabilize. -/

section WholePolydisc

open Metric

variable {ι : Type*}

section OneForms

variable [Fintype ι] [DecidableEq ι] [CompleteSpace F]

/-- **The `bar∂`-Poincaré lemma for `(0,1)`-forms on polydiscs.** A smooth `bar∂`-closed
`(0,1)`-form `∑ j, f_j d(conj z_j)` on the polydisc `∏ B(c_i, r_i)`, with coefficients in a
complex Banach space, is `bar∂`-exact on the whole polydisc: some `u`, smooth there, satisfies
`∂u/∂(conj z_j) = f_j` for every `j`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_single_eq_of_polydisc {c : ι → ℂ}
    {r : ι → ℝ} {f : ι → (ι → ℂ) → F}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) (univ.pi fun i ↦ ball (c i) (r i)))
    (hclosed : ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ i j,
      conjWirtingerDeriv (f j) z (Pi.single i 1) = conjWirtingerDeriv (f i) z (Pi.single j 1)) :
    ∃ u : (ι → ℂ) → F, ContDiffOn ℝ ∞ u (univ.pi fun i ↦ ball (c i) (r i)) ∧
      ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ j,
        conjWirtingerDeriv u z (Pi.single j 1) = f j z := by
  obtain ⟨s, hs_succ, hs_mono, hs_lt, hs_cov⟩ := exists_polyradius_exhaustion c r
  set D : (ι → ℝ) → Set (ι → ℂ) := fun ρ ↦ univ.pi fun i ↦ ball (c i) (ρ i)
  have hDo (ρ : ι → ℝ) : IsOpen (D ρ) := isOpen_set_pi finite_univ fun i _ ↦ isOpen_ball
  have hDmono {ρ ρ' : ι → ℝ} (h : ρ ≤ ρ') : D ρ ⊆ D ρ' :=
    pi_mono fun i _ ↦ ball_subset_ball (h i)
  -- Local solutions `h k`, smooth with `bar∂ (h k) = f` on `D (s (k + 1))`.
  have hloc (k : ℕ) : ∃ h : (ι → ℂ) → F, ContDiffOn ℝ ∞ h (D (s (k + 1))) ∧
      ∀ z ∈ D (s (k + 1)), ∀ j, conjWirtingerDeriv h z (Pi.single j 1) = f j z := by
    obtain ⟨u, hu⟩ := exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi
      (fun i ↦ isOpen_ball) hf hclosed (fun i ↦ isCompact_closedBall (c i) (s (k + 1) i))
      fun i ↦ closedBall_subset_ball (hs_lt (k + 1) i)
    have hu' {z : ι → ℂ} (hz : z ∈ D (s (k + 1))) :=
      hu.self_of_nhdsSet z (pi_mono (fun i _ ↦ ball_subset_closedBall) hz)
    exact ⟨u, fun z hz ↦ (hu' hz).1.contDiffWithinAt, fun z hz ↦ (hu' hz).2⟩
  choose h hh hh_eq using hloc
  have hdiffAt {k : ℕ} {z : ι → ℂ} (hz : z ∈ D (s (k + 1))) : DifferentiableAt ℝ (h k) z :=
    ((hh k).contDiffAt ((hDo _).mem_nhds hz)).differentiableAt (by simp)
  -- Consecutive local solutions differ by a holomorphic function.
  have hdiff (k : ℕ) : DifferentiableOn ℂ (h (k + 1) - h k) (D (s (k + 1))) := fun z hz ↦ by
    have hz' : z ∈ D (s (k + 1 + 1)) := hDmono (hs_mono (k + 1).le_succ) hz
    refine ((differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero
      ((hdiffAt hz').sub (hdiffAt hz))).2 fun j ↦ ?_).differentiableWithinAt
    rw [conjWirtingerDeriv_sub (hdiffAt hz') (hdiffAt hz), sub_apply,
      hh_eq (k + 1) z hz' j, hh_eq k z hz j, sub_self]
  -- Polynomial corrections `P k`, approximating the differences within `2⁻ᵏ` on `D (s k)`.
  have happrox (k : ℕ) : ∃ P : (ι → ℂ) → F, Differentiable ℂ P ∧
      ∀ z ∈ univ.pi fun i ↦ closedBall (c i) (s k i),
        ‖(h (k + 1) - h k) z - P z‖ < (1 / 2 : ℝ) ^ k :=
    (hdiff k).exists_differentiable_norm_sub_lt_of_pi (hs_succ k) (by positivity)
  choose P hP hP_lt using happrox
  -- On `D (s m)`, the corrected limit is `h m` plus a holomorphic function.
  set u : (ι → ℂ) → F := fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - P k) z
  have hkey (m : ℕ) : ∃ K : (ι → ℂ) → F, DifferentiableOn ℂ K (D (s m)) ∧
      EqOn u (h m + K) (D (s m)) :=
    (hDo _).exists_differentiableOn_eqOn_add_tsum (fun k ↦ (hP k).differentiableOn)
      (fun k hk ↦ (hdiff k).mono (hDmono (hs_mono (hk.trans k.le_succ))))
      fun k hk z hz ↦ (hP_lt k z fun i _ ↦ ball_subset_closedBall
        (ball_subset_ball (hs_mono hk i) (hz i trivial))).le
  -- Every point lies in some `D (s m)`, where `u` is `h m` plus a holomorphic function.
  exact ⟨u, contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add (G := u) (U := D r)
    (v := fun j ↦ Pi.single j 1) (f := f) (n := ∞) (by simp) fun z hz ↦ by
      obtain ⟨m, hm⟩ := hs_cov z hz
      obtain ⟨K, hK, huK⟩ := hkey m
      have hsub : D (s m) ⊆ D (s (m + 1)) := hDmono (hs_mono m.le_succ)
      exact ⟨D (s m), hDo _, hm, h m, K, (hh m).mono hsub,
        fun w hw ↦ hh_eq m w (hsub hw), hK.contDiffOn_of_finiteDimensional (hDo _), huK⟩⟩

end OneForms

section Forms

variable [LinearOrder ι] [Fintype ι] [CompleteSpace F]

/-- A smooth `bar∂`-closed `(0,q+1)`-form on the polydisc `∏ B(c_i, r_i)` is, on the concentric
polydisc of every smaller polyradius, `bar∂` of a `(0,q)`-form whose coefficients are smooth on all
of `ι → ℂ`. -/
private theorem exists_contDiff_delBarCoeff_eq_of_lt {q : ℕ} {c : ι → ℂ} {r ρ : ι → ℝ}
    (hρ : ∀ i, ρ i < r i) {f : Finset ι → (ι → ℂ) → F}
    (hf : ∀ I, #I = q + 1 → ContDiffOn ℝ ∞ (f I) (univ.pi fun i ↦ ball (c i) (r i)))
    (hclosed : ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ I, #I = q + 2 →
      delBarCoeff f I z = 0) :
    ∃ u : Finset ι → (ι → ℂ) → F, (∀ J, ContDiff ℝ ∞ (u J)) ∧
      ∀ z ∈ univ.pi fun i ↦ ball (c i) (ρ i), ∀ I, #I = q + 1 → delBarCoeff u I z = f I z := by
  have hK : IsCompact (univ.pi fun i ↦ closedBall (c i) (ρ i)) :=
    isCompact_univ_pi fun i ↦ isCompact_closedBall (c i) (ρ i)
  obtain ⟨u, hu⟩ := exists_contDiffAt_delBarCoeff_eventually_eq_of_pi (fun i ↦ isOpen_ball) hf
    hclosed (fun i ↦ isCompact_closedBall (c i) (ρ i)) fun i ↦ closedBall_subset_ball (hρ i)
  obtain ⟨V, hV, hKV, hVu⟩ := eventually_nhdsSet_iff_exists.1 hu
  -- Extend the coefficients from a neighbourhood of the closed polydisc to all of `ι → ℂ`.
  have hext (J : Finset ι) : ∃ g : (ι → ℂ) → F, ContDiff ℝ ∞ g ∧
      ∀ z ∈ univ.pi fun i ↦ closedBall (c i) (ρ i), g =ᶠ[𝓝 z] u J := by
    have huV : ContDiffOn ℝ ∞ (u J) V := fun z hz ↦ ((hVu z hz).1 J).contDiffWithinAt
    obtain ⟨g, hg, -, -, -, hgu⟩ := huV.exists_contDiff_eventuallyEq_on_isCompact hK hV hKV
    exact ⟨g, hg, hgu⟩
  choose g hg hgu using hext
  refine ⟨g, hg, fun z hz I hI ↦ ?_⟩
  have hz' : z ∈ univ.pi fun i ↦ closedBall (c i) (ρ i) :=
    pi_mono (fun i _ ↦ ball_subset_closedBall) hz
  rw [delBarCoeff_congr fun j _ ↦ hgu _ z hz', (hVu z (hKV hz')).2 I hI]

/-- **The correction step.** Let `u` and `v` be `(0,q+1)`-forms with smooth coefficients whose
`bar∂` agree on the polydisc `∏ B(c_i, σ_i)`. Subtracting from `u` the `bar∂` of a `(0,q)`-form
gives a form `v'` with smooth coefficients and the same `bar∂` as `u` everywhere, whose coefficients
agree with those of `v` on the concentric polydisc of every smaller polyradius `ρ`. -/
private theorem exists_delBarCoeff_eq_and_eq_of_delBarCoeff_eq {q : ℕ} {c : ι → ℂ}
    {ρ σ : ι → ℝ} (hρσ : ∀ i, ρ i < σ i) {u v : Finset ι → (ι → ℂ) → F}
    (hu : ∀ J, ContDiff ℝ ∞ (u J)) (hv : ∀ J, ContDiff ℝ ∞ (v J))
    (huv : ∀ z ∈ univ.pi fun i ↦ ball (c i) (σ i), ∀ I, #I = q + 2 →
      delBarCoeff u I z = delBarCoeff v I z) :
    ∃ v' : Finset ι → (ι → ℂ) → F, (∀ J, ContDiff ℝ ∞ (v' J)) ∧
      (∀ z I, delBarCoeff v' I z = delBarCoeff u I z) ∧
      ∀ z ∈ univ.pi fun i ↦ ball (c i) (ρ i), ∀ J, #J = q + 1 → v' J z = v J z := by
  have hd {w : Finset ι → (ι → ℂ) → F} (hw : ∀ J, ContDiff ℝ ∞ (w J)) (I : Finset ι)
      (z : ι → ℂ) : ∀ j ∈ I, DifferentiableAt ℝ (w (I.erase j)) z :=
    fun j _ ↦ (hw _).differentiable (by simp) z
  -- `u - v` is `bar∂`-closed on `∏ B(c_i, σ_i)`, hence `bar∂ g` on `∏ B(c_i, ρ_i)`.
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_delBarCoeff_eq_of_lt (q := q) hρσ (f := u - v)
    (fun J _ ↦ ((hu J).sub (hv J)).contDiffOn) fun z hz I hI ↦ by
      rw [delBarCoeff_sub (hd hu I z) (hd hv I z), huv z hz I hI, sub_self]
  have hdg (J : Finset ι) : ContDiff ℝ ∞ (delBarCoeff g J) :=
    contDiff_iff_contDiffAt.2 fun z ↦ contDiffAt_delBarCoeff (fun j _ ↦ (hg _).contDiffAt)
      (by simp)
  refine ⟨u - delBarCoeff g, fun J ↦ (hu J).sub (hdg J), fun z I ↦ ?_, fun z hz J hJ ↦ ?_⟩
  · rw [delBarCoeff_sub (hd hu I z) (hd hdg I z),
      delBarCoeff_delBarCoeff fun j _ i _ ↦ ((hg _).of_le (by simp)).contDiffAt, sub_zero]
  · rw [Pi.sub_apply, Pi.sub_apply, hgf z hz J hJ, Pi.sub_apply, Pi.sub_apply, sub_sub_cancel]

/-- The case of `(0,q+2)`-forms of `TauCeti.exists_contDiffOn_delBarCoeff_eq_of_polydisc`. -/
private theorem exists_contDiffOn_delBarCoeff_eq_of_polydisc_succ {q : ℕ} {c : ι → ℂ}
    {r : ι → ℝ} {f : Finset ι → (ι → ℂ) → F}
    (hf : ∀ I, #I = q + 2 → ContDiffOn ℝ ∞ (f I) (univ.pi fun i ↦ ball (c i) (r i)))
    (hclosed : ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ I, #I = q + 3 →
      delBarCoeff f I z = 0) :
    ∃ u : Finset ι → (ι → ℂ) → F,
      (∀ J, ContDiffOn ℝ ∞ (u J) (univ.pi fun i ↦ ball (c i) (r i))) ∧
      ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ I, #I = q + 2 → delBarCoeff u I z = f I z := by
  classical
  obtain ⟨s, hs_succ, hs_mono, hs_lt, hs_cov⟩ := exists_polyradius_exhaustion c r
  set D : (ι → ℝ) → Set (ι → ℂ) := fun ρ ↦ univ.pi fun i ↦ ball (c i) (ρ i)
  have hDo (ρ : ι → ℝ) : IsOpen (D ρ) := isOpen_set_pi finite_univ fun i _ ↦ isOpen_ball
  have hDmono {ρ ρ' : ι → ℝ} (h : ρ ≤ ρ') : D ρ ⊆ D ρ' :=
    pi_mono fun i _ ↦ ball_subset_ball (h i)
  -- `Sol k v`: the coefficients of `v` are smooth, and `bar∂ v = f` on `D (s (k + 1))`.
  let Sol (k : ℕ) (v : Finset ι → (ι → ℂ) → F) : Prop :=
    (∀ J, ContDiff ℝ ∞ (v J)) ∧ ∀ z ∈ D (s (k + 1)), ∀ I, #I = q + 2 → delBarCoeff v I z = f I z
  have hloc (k : ℕ) : ∃ v, Sol k v :=
    exists_contDiff_delBarCoeff_eq_of_lt (hs_lt (k + 1)) hf hclosed
  -- A solution at stage `k + 1` agreeing on `D (s k)` with a given one at stage `k`.
  have hstep (k : ℕ) (v : {v // Sol k v}) : ∃ v' : {v' // Sol (k + 1) v'},
      ∀ z ∈ D (s k), ∀ J, #J = q + 1 → v'.val J z = v.val J z := by
    obtain ⟨u, hu, huf⟩ := hloc (k + 1)
    obtain ⟨v', hv', hv'u, hv'v⟩ := exists_delBarCoeff_eq_and_eq_of_delBarCoeff_eq (hs_succ k) hu
      v.property.1 fun z hz I hI ↦ by
        rw [huf z (hDmono (hs_mono (k + 1).le_succ) hz) I hI, v.property.2 z hz I hI]
    exact ⟨⟨v', hv', fun z hz I hI ↦ by rw [hv'u z I, huf z hz I hI]⟩, hv'v⟩
  obtain ⟨v₀, hv₀⟩ := hloc 0
  choose next hnext using hstep
  -- The corrected solutions `w k`, which stabilize on each `D (s m)`.
  let w (k : ℕ) : {v // Sol k v} := Nat.rec (motive := fun k ↦ {v // Sol k v}) ⟨v₀, hv₀⟩ next k
  have hstab {m k : ℕ} (hmk : m ≤ k) {z : ι → ℂ} (hz : z ∈ D (s m)) {J : Finset ι}
      (hJ : #J = q + 1) : (w k).val J z = (w m).val J z := by
    induction k, hmk using Nat.le_induction with
    | base => rfl
    | succ k hmk ih => exact (hnext k (w k) z (hDmono (hs_mono hmk) hz) J hJ).trans ih
  -- The limit: at a point, the value of `w m` for the first `m` with the point in `D (s m)`.
  let N (z : ι → ℂ) : ℕ := if h : ∃ m, z ∈ D (s m) then Nat.find h else 0
  let u (J : Finset ι) (z : ι → ℂ) : F := if #J = q + 1 then (w (N z)).val J z else 0
  have hu {m : ℕ} {z : ι → ℂ} (hz : z ∈ D (s m)) {J : Finset ι} (hJ : #J = q + 1) :
      u J z = (w m).val J z := by
    have h : ∃ m, z ∈ D (s m) := ⟨m, hz⟩
    simp only [u, N, hJ, ↓reduceIte]
    rw [dite_eq_left h]
    exact (hstab (Nat.find_min' h hz) (Nat.find_spec h) hJ).symm
  refine ⟨u, fun J z hz ↦ ?_, fun z hz I hI ↦ ?_⟩
  · obtain ⟨m, hm⟩ := hs_cov z hz
    by_cases hJ : #J = q + 1
    · refine (((w m).property.1 J).contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [(hDo _).mem_nhds hm] with y hy using hu hy hJ
    · simp only [u, hJ, ↓reduceIte]
      exact contDiffWithinAt_const
  · obtain ⟨m, hm⟩ := hs_cov z hz
    rw [delBarCoeff_congr (w := (w m).val) fun j hj ↦ ?_,
      (w m).property.2 z (hDmono (hs_mono m.le_succ) hm) I hI]
    filter_upwards [(hDo _).mem_nhds hm] with y hy
    exact hu hy (by rw [Finset.card_erase_of_mem hj, hI]; rfl)

/-- **The Dolbeault–Grothendieck lemma for `(0,q)`-forms on polydiscs.** A smooth `bar∂`-closed
`(0,q+1)`-form on the polydisc `∏ B(c_i, r_i)`, with coefficients in a complex Banach space, is
`bar∂`-exact on the whole polydisc: some `(0,q)`-form `u`, smooth there, satisfies `bar∂ u = f`
there. -/
theorem exists_contDiffOn_delBarCoeff_eq_of_polydisc {q : ℕ} {c : ι → ℂ} {r : ι → ℝ}
    {f : Finset ι → (ι → ℂ) → F}
    (hf : ∀ I, #I = q + 1 → ContDiffOn ℝ ∞ (f I) (univ.pi fun i ↦ ball (c i) (r i)))
    (hclosed : ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ I, #I = q + 2 →
      delBarCoeff f I z = 0) :
    ∃ u : Finset ι → (ι → ℂ) → F,
      (∀ J, ContDiffOn ℝ ∞ (u J) (univ.pi fun i ↦ ball (c i) (r i))) ∧
      ∀ z ∈ univ.pi fun i ↦ ball (c i) (r i), ∀ I, #I = q + 1 → delBarCoeff u I z = f I z := by
  cases q with
  | succ q => exact exists_contDiffOn_delBarCoeff_eq_of_polydisc_succ hf hclosed
  | zero =>
    -- A `(0,1)`-form is a family of functions indexed by the singletons.
    obtain ⟨u, hu, huf⟩ := exists_contDiffOn_conjWirtingerDeriv_apply_single_eq_of_polydisc
      (f := fun j ↦ f {j}) (fun j ↦ hf {j} (Finset.card_singleton j)) fun z hz i j ↦ by
        rcases lt_trichotomy i j with h | rfl | h
        · have := hclosed z hz {i, j} (Finset.card_pair h.ne)
          rwa [delBarCoeff_pair _ h, sub_eq_zero] at this
        · rfl
        · have := hclosed z hz {j, i} (Finset.card_pair h.ne)
          rw [delBarCoeff_pair _ h, sub_eq_zero] at this
          exact this.symm
    refine ⟨fun _ ↦ u, fun _ ↦ hu, fun z hz I hI ↦ ?_⟩
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hI
    rw [delBarCoeff_singleton, huf z hz j]

end Forms

end WholePolydisc

end TauCeti
