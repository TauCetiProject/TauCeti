/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Potential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# The `bar∂`-Poincaré lemma on polydiscs

On the coordinate space `ι → ℂ` of a finite index type `ι`, write
`∂f/∂(conj z_j) = conjWirtingerDeriv f z (Pi.single j 1)` for the conjugate Wirtinger derivative
in the `j`-th coordinate. A `(0,1)`-form `∑ j, f_j d(conj z_j)` with coefficients in a complex
Banach space `F` is `bar∂`-closed when `∂f_j/∂(conj z_i) = ∂f_i/∂(conj z_j)` for all `i, j`.

This file proves the Dolbeault–Grothendieck lemma for such forms in coordinates: a smooth
`bar∂`-closed `(0,1)`-form on a product domain `∏ U_i` of open sets `U_i ⊆ ℂ`, in particular on
a polydisc, is `bar∂`-exact near every compact product `∏ K_i` with `K_i ⊆ U_i`. That is, some
smooth `u` satisfies `∂u/∂(conj z_j) = f_j` for every `j` there.

The proof eliminates one conjugate variable at a time, as in Hörmander and Griffiths–Harris. The
elimination step
`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_single_eventually_eq_of_pi` solves
`∂v/∂(conj z_k) = g` in one coordinate `z_k`. If `g` is holomorphic in a set `T` of other
coordinates, the solution `v` can be chosen holomorphic in those coordinates as well; it is
`Cⁿ`, like `g`. This is the one-variable solver
`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_holomorphic_param`
with the coordinates outside `{k} ∪ T` as smooth parameters and those in `T` as holomorphic
parameters. The step applies to coefficients in any complex Banach space, so it also performs the
elimination for forms of higher degree, whose coefficient families are vector valued.

## Main results

* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_single_eventually_eq_of_pi`: the
  elimination step, solving `∂v/∂(conj z_k) = g` and keeping holomorphy in the coordinates where
  `g` is holomorphic.
* `TauCeti.exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi`: a smooth
  `bar∂`-closed `(0,1)`-form on a product of open subsets of `ℂ` is `bar∂`-exact near every
  compact product inside it.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_single_eq_of_polydisc`: the same on
  polydiscs. A smooth `bar∂`-closed `(0,1)`-form on a polydisc of polyradius `r` is `bar∂`-exact
  on the concentric polydisc of every smaller polyradius.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 2.3.3.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §2
  (the `bar∂`-Poincaré lemma in several variables).
-/

public section

open Complex Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {ι : Type*} [DecidableEq ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

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

/-! ### The `bar∂`-Poincaré lemma for `(0,1)`-forms -/

omit [CompleteSpace F] in
/-- Subtracting the `bar∂` of a `C²` map keeps a `(0,1)`-form `bar∂`-closed at a point. -/
private theorem conjWirtingerDeriv_sub_conjWirtingerDeriv_comm {f : ι → (ι → ℂ) → F}
    {v : (ι → ℂ) → F} {z : ι → ℂ} (hf : ∀ j, DifferentiableAt ℝ (f j) z)
    (hv : ContDiffAt ℝ 2 v z)
    (hclosed : ∀ i j,
      conjWirtingerDeriv (f j) z (Pi.single i 1) = conjWirtingerDeriv (f i) z (Pi.single j 1))
    (i j : ι) :
    conjWirtingerDeriv (f j - fun y ↦ conjWirtingerDeriv v y (Pi.single j 1)) z
        (Pi.single i 1) =
      conjWirtingerDeriv (f i - fun y ↦ conjWirtingerDeriv v y (Pi.single i 1)) z
        (Pi.single j 1) := by
  have hdv (a : ι → ℂ) : DifferentiableAt ℝ (fun y ↦ conjWirtingerDeriv v y a) z :=
    (hv.hasFDerivAt_conjWirtingerDeriv_apply a).differentiableAt
  rw [conjWirtingerDeriv_sub (hf j) (hdv _), conjWirtingerDeriv_sub (hf i) (hdv _), sub_apply,
    sub_apply, hclosed i j, conjWirtingerDeriv_conjWirtingerDeriv_comm hv]

/-- The induction behind
`TauCeti.exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi`, on the finite set
`S` of coordinates whose coefficients may be nonzero. -/
private theorem exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi_of_eq_zero
    (S : Finset ι) :
    ∀ {U : ι → Set ℂ}, (∀ i, IsOpen (U i)) → ∀ {f : ι → (ι → ℂ) → F},
      (∀ j, ContDiffOn ℝ ∞ (f j) (univ.pi U)) →
      (∀ z ∈ univ.pi U, ∀ i j,
        conjWirtingerDeriv (f j) z (Pi.single i 1) = conjWirtingerDeriv (f i) z (Pi.single j 1)) →
      (∀ j ∉ S, ∀ z ∈ univ.pi U, f j z = 0) → ∀ {K : ι → Set ℂ}, (∀ i, IsCompact (K i)) →
      (∀ i, K i ⊆ U i) → ∃ u : (ι → ℂ) → F, ∀ᶠ z in 𝓝ˢ (univ.pi K),
        ContDiffAt ℝ ∞ u z ∧ ∀ j, conjWirtingerDeriv u z (Pi.single j 1) = f j z := by
  induction S using Finset.induction_on with
  | empty =>
    intro U hU f _ _ hS K _ hKU
    have hpi : IsOpen (univ.pi U) := isOpen_set_pi finite_univ fun i _ ↦ hU i
    refine ⟨0, ?_⟩
    filter_upwards [hpi.mem_nhdsSet.2 (pi_mono fun i _ ↦ hKU i)] with z hz
    refine ⟨contDiffAt_const, fun j ↦ ?_⟩
    simp [hS j (Finset.notMem_empty j) z hz]
  | insert k S hkS ih =>
    intro U hU f hf hclosed hS K hK hKU
    have hpi : IsOpen (univ.pi U) := isOpen_set_pi finite_univ fun i _ ↦ hU i
    -- Shrink each `U_i` to an open `W_i ⊇ K_i` with compact closure inside `U_i`.
    choose W hWo hKW hWU hWc using fun i ↦
      exists_open_between_and_isCompact_closure (hK i) (hU i) (hKU i)
    have hWpi : IsOpen (univ.pi W) := isOpen_set_pi finite_univ fun i _ ↦ hWo i
    have hWsub : univ.pi W ⊆ univ.pi U :=
      pi_mono fun i _ ↦ subset_closure.trans (hWU i)
    -- Eliminate `d(conj z_k)`, keeping holomorphy in the coordinates outside `insert k S`.
    have hT : k ∉ (insert k S)ᶜ := by simp
    obtain ⟨v, hv, hvT, hvk⟩ :=
      exists_contDiffOn_conjWirtingerDeriv_apply_single_eventually_eq_of_pi le_top hU hT
        (hWc k) (hWU k) (hf k) fun z hz j hj ↦ by
        have h : f j =ᶠ[𝓝 z] fun _ ↦ 0 :=
          eventually_of_mem (hpi.mem_nhds hz) (hS j (Finset.mem_compl.1 hj))
        simp [hclosed z hz j k, h.conjWirtingerDeriv_eq]
    have hvk' : ∀ z ∈ univ.pi W, conjWirtingerDeriv v z (Pi.single k 1) = f k z := fun z hz ↦
      hvk.self_of_nhdsSet (z k) (subset_closure (hz k (mem_univ k))) z (hWsub hz) rfl
    have hv2 {z : ι → ℂ} (hz : z ∈ univ.pi U) : ContDiffAt ℝ ∞ v z :=
      hv.contDiffAt (hpi.mem_nhds hz)
    have hvd {z : ι → ℂ} (hz : z ∈ univ.pi U) : DifferentiableAt ℝ v z :=
      (hv2 hz).differentiableAt (by simp)
    have hdv (j : ι) : ContDiffOn ℝ ∞ (fun z ↦ conjWirtingerDeriv v z (Pi.single j 1))
        (univ.pi U) := hv.conjWirtingerDeriv_apply_of_isOpen hpi (by simp) _
    -- The remaining form `f - bar∂ v` is `bar∂`-closed and involves only the coordinates in `S`.
    set f' : ι → (ι → ℂ) → F := fun j ↦ f j - fun z ↦ conjWirtingerDeriv v z (Pi.single j 1)
      with hf'
    have hclosed' : ∀ z ∈ univ.pi W, ∀ i j,
        conjWirtingerDeriv (f' j) z (Pi.single i 1) =
          conjWirtingerDeriv (f' i) z (Pi.single j 1) := by
      intro z hz i j
      have hzU := hWsub hz
      exact conjWirtingerDeriv_sub_conjWirtingerDeriv_comm
        (fun j ↦ ((hf j).contDiffAt (hpi.mem_nhds hzU)).differentiableAt (by simp))
        ((hv2 hzU).of_le (by simp)) (hclosed z hzU) i j
    have hS' : ∀ j ∉ S, ∀ z ∈ univ.pi W, f' j z = 0 := by
      intro j hj z hz
      by_cases hjk : j = k
      · subst hjk
        simp [hf', hvk' z hz]
      · have hj' : j ∈ (insert k S)ᶜ := by simp [hjk, hj]
        simp [hf', hS j (Finset.mem_compl.1 hj') z (hWsub hz), hvT z (hWsub hz) j hj']
    obtain ⟨w, hw⟩ := ih hWo (fun j ↦ ((hf j).sub (hdv j)).mono hWsub) hclosed' hS' hK hKW
    refine ⟨v + w, ?_⟩
    filter_upwards [hw, hWpi.mem_nhdsSet.2 (pi_mono fun i _ ↦ hKW i)] with z hwz hz
    refine ⟨(hv2 (hWsub hz)).add hwz.1, fun j ↦ ?_⟩
    rw [conjWirtingerDeriv_add (hvd (hWsub hz)) (hwz.1.differentiableAt (by simp)),
      add_apply, hwz.2 j, add_sub_cancel]

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
      ContDiffAt ℝ ∞ u z ∧ ∀ j, conjWirtingerDeriv u z (Pi.single j 1) = f j z :=
  exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi_of_eq_zero Finset.univ hU
    hf hclosed (fun j hj ↦ absurd (Finset.mem_univ j) hj) hK hKU

/-- **The `bar∂`-Poincaré lemma for `(0,1)`-forms on polydiscs.** A smooth `bar∂`-closed
`(0,1)`-form `∑ j, f_j d(conj z_j)` on the polydisc `∏ B(c_i, r_i)` is `bar∂`-exact on every
concentric polydisc `∏ B(c_i, r'_i)` with `r'_i < r_i`: some `u`, smooth there, satisfies
`∂u/∂(conj z_j) = f_j` for every `j`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_single_eq_of_polydisc {c : ι → ℂ}
    {r r' : ι → ℝ} (hr : ∀ i, r' i < r i) {f : ι → (ι → ℂ) → F}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) (univ.pi fun i ↦ Metric.ball (c i) (r i)))
    (hclosed : ∀ z ∈ univ.pi fun i ↦ Metric.ball (c i) (r i), ∀ i j,
      conjWirtingerDeriv (f j) z (Pi.single i 1) = conjWirtingerDeriv (f i) z (Pi.single j 1)) :
    ∃ u : (ι → ℂ) → F, ContDiffOn ℝ ∞ u (univ.pi fun i ↦ Metric.ball (c i) (r' i)) ∧
      ∀ z ∈ univ.pi fun i ↦ Metric.ball (c i) (r' i), ∀ j,
        conjWirtingerDeriv u z (Pi.single j 1) = f j z := by
  obtain ⟨u, hu⟩ :=
    exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi
      (fun i ↦ Metric.isOpen_ball) hf hclosed (fun i ↦ isCompact_closedBall (c i) (r' i))
      fun i ↦ Metric.closedBall_subset_ball (hr i)
  have hsub : (univ.pi fun i ↦ Metric.ball (c i) (r' i)) ⊆
      univ.pi fun i ↦ Metric.closedBall (c i) (r' i) :=
    pi_mono fun i _ ↦ Metric.ball_subset_closedBall
  exact ⟨u, fun z hz ↦ (hu.self_of_nhdsSet z (hsub hz)).1.contDiffWithinAt,
    fun z hz ↦ (hu.self_of_nhdsSet z (hsub hz)).2⟩

end TauCeti
