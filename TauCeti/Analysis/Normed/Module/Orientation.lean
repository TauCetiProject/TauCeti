/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.LinearAlgebra.Orientation.Basic
public import TauCeti.LinearAlgebra.Orientation.ShortExact
import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Orientation.Basis

/-!
# Continuous families of linear maps transport orientations alike

Let `L x : E → F` be a family of continuous linear maps between real normed spaces, continuous at
`x₀`, whose value at `x₀` is a linear equivalence `f₀`. Near `x₀`, every linear equivalence equal
to `L x` transports an orientation of `E` as `f₀` does
(`Orientation.eventually_map_eq_map_of_continuousAt`): relative to `f₀`, the determinant of `L x`
is `1` at `x₀`, hence positive nearby.

This is the local constancy step behind continuous families of orientations, such as orientations
of vector bundles transported along fibrewise isomorphisms.

Likewise, bases converging to a basis `B₀` eventually have the orientation of `B₀`
(`Module.Basis.eventually_orientation_eq_of_tendsto`), and the same holds for the orientations of
kernels. Let `L x : E → F` be continuous linear maps out of a finite-dimensional space, tending
along a filter to a surjection `L₀`. They are eventually surjective
(`TauCeti.isOpen_setOf_surjective`), and orientations of `E` and `F` orient their kernels,
subspace first (`Orientation.shortExactLeft`). Read on bases of the kernels converging to a basis
of `ker L₀`, these orientations eventually agree with that of `ker L₀`
(`Orientation.eventually_orientation_eq_shortExactLeft_iff_of_tendsto`): completing the kernel
bases by a fixed family of lifts of a basis of `F` along `L₀` gives bases of `E` converging to a
basis, which lift bases of `F` of constant orientation along `L x`.

This is the input for orienting the spaces of trajectories of a Morse–Smale gradient flow
coherently: the tangent space of a space of trajectories is the kernel of a surjective comparison
map depending continuously on the trajectory, and its orientation is induced from those of the
unstable manifolds. The filter form also computes the limit of these orientations along
trajectories converging to a broken one, where the comparison maps tend to a map attached to the
broken trajectory rather than to a point of the family.

In a line, two vectors of the same norm giving the same orientation are equal
(`TauCeti.eq_of_orientation_basisSingleton_eq`).

## Main results

* `Orientation.eventually_map_eq_map_of_continuousAt`: near `x₀`, the linear equivalences given by
  a continuous family `L` transport an orientation as its value at `x₀` does.
* `Module.Basis.eventually_orientation_eq_of_tendsto`: bases converging to a basis eventually have
  its orientation.
* `Orientation.eventually_orientation_eq_shortExactLeft_iff_of_tendsto`: the orientations of the
  kernels of a convergent family of surjections, read on convergent bases, are eventually those of
  the limit.
* `TauCeti.eq_of_orientation_basisSingleton_eq`: a unit vector of a line is determined by the
  orientation it gives.
-/

public section

open Filter Module
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ι : Type*} [Fintype ι]

/-- **Orientation transport is locally constant along a continuous family.** Let `L` be a family of
continuous linear maps `E → F`, continuous at `x₀` with value the linear equivalence `f₀` there.
Near `x₀`, every linear equivalence `f` equal to `L x` transports an orientation `c` of `E` as `f₀`
does. Continuity of `L` is needed only when `E` is finite-dimensional: otherwise `ι` is empty, and
any two linear equivalences transport `c` alike. -/
theorem Orientation.eventually_map_eq_map_of_continuousAt {X : Type*} [TopologicalSpace X]
    {x₀ : X} (hι : Fintype.card ι = finrank ℝ E) (c : Orientation ℝ E ι) {f₀ : E ≃L[ℝ] F}
    {L : X → E →L[ℝ] F} (hL : FiniteDimensional ℝ E → ContinuousAt L x₀)
    (hL₀ : L x₀ = f₀) :
    ∀ᶠ x in 𝓝 x₀, ∀ f : E ≃L[ℝ] F, (f : E →L[ℝ] F) = L x →
      Orientation.map ι f.toLinearEquiv c = Orientation.map ι f₀.toLinearEquiv c := by
  rcases isEmpty_or_nonempty ι with hι₀ | hι₀
  · -- With `ι` empty, transport along any self-equivalence of `E` fixes every orientation.
    refine Eventually.of_forall fun x f _ ↦ ?_
    have h := Orientation.map_of_isEmpty (x := c)
      (f := f.toLinearEquiv.trans f₀.toLinearEquiv.symm)
    rw [Orientation.map_trans, ← Orientation.map_symm, Equiv.symm_apply_eq] at h
    exact h
  -- Otherwise `E` is finite-dimensional, and the determinant of `f₀⁻¹ ∘ L x`, which is `1` at
  -- `x₀`, is positive near `x₀`.
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (hι ▸ Fintype.card_pos)
  let K (x : X) : E →L[ℝ] E := (f₀.symm : F →L[ℝ] E).comp (L x)
  have hK₀ : (K x₀).det = 1 := by
    rw [ContinuousLinearMap.det, show K x₀ = ContinuousLinearMap.id ℝ E by ext v; simp [K, hL₀],
      ContinuousLinearMap.coe_id, LinearMap.det_id]
  have hK : ContinuousAt K x₀ := ContinuousAt.clm_comp continuousAt_const (hL this)
  filter_upwards [(ContinuousLinearMap.continuous_det.continuousAt.comp hK).eventually
    (lt_mem_nhds (hK₀ ▸ one_pos))] with x hx f hf
  refine (Orientation.map_eq_map_iff_det_pos c _ _ hι).mpr ?_
  have hKf : K x = (f.trans f₀.symm : E →L[ℝ] E) := by
    ext v
    simp [K, ← hf]
  rw [Function.comp_apply, hKf] at hx
  simpa [ContinuousLinearMap.det] using hx

/-- Two vectors of the same norm in a line that give the same orientation are equal. -/
theorem TauCeti.eq_of_orientation_basisSingleton_eq {V ι : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Unique ι] [Fintype ι] [DecidableEq ι] (hV : Module.finrank ℝ V = 1)
    {v w : V} (hn : ‖w‖ = ‖v‖) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : (FiniteDimensional.basisSingleton ι hV w hw).orientation =
      (FiniteDimensional.basisSingleton ι hV v hv).orientation) :
    w = v := by
  refine (eq_or_eq_neg_of_norm_eq_of_finrank_eq_one hV hn).resolve_right fun hwv ↦ ?_
  subst hwv
  rw [TauCeti.orientation_basisSingleton_neg hV hw] at h
  exact Module.Ray.ne_neg_self _ h.symm

/-! ### Orientations of the kernels of a continuous family of surjections -/

section Kernel

/-- **Nearby bases have the same orientation.** If families of vectors `w x` tend along a filter to
the vectors of a basis `B₀` of a real normed space, then eventually every basis with vectors `w x`
has the orientation of `B₀`: relative to `B₀`, their determinant tends to `1`. -/
theorem Module.Basis.eventually_orientation_eq_of_tendsto [DecidableEq ι] {α : Type*}
    {l : Filter α} (B₀ : Basis ι ℝ E) {w : α → ι → E} (hw : Tendsto w l (𝓝 ⇑B₀)) :
    ∀ᶠ x in l, ∀ B : Basis ι ℝ E, ⇑B = w x → B.orientation = B₀.orientation := by
  have h := ((map_continuous B₀.continuousDet).tendsto _).comp hw
  simp only [Function.comp_def, Basis.continuousDet_apply, B₀.det_self] at h
  filter_upwards [h.eventually (lt_mem_nhds one_pos)] with x hx B hB
  exact ((B₀.orientation_eq_iff_det_pos B).2 (hB ▸ hx)).symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {a c : ℕ}

/-- The orientation of the kernels of a convergent family of surjections, read on bases converging
to a basis of the limiting kernel, measured against a fixed basis `e` of the target. This is the
case of `Orientation.eventually_orientation_eq_shortExactLeft_iff_of_tendsto` with `p` the
orientation of a basis, for every orientation of the source at once. -/
private theorem eventually_orientation_eq_shortExactLeft_iff_of_tendsto_basis {α : Type*}
    {l : Filter α} {L : α → E →L[ℝ] F} {L₀ : E →L[ℝ] F} (hL : Tendsto L l (𝓝 L₀))
    (hL₀ : Function.Surjective L₀) (b₀ : Basis (Fin a) ℝ (LinearMap.ker L₀.toLinearMap))
    {v : α → Fin a → E} (hv : Tendsto v l (𝓝 fun i ↦ (b₀ i : E))) (hc : finrank ℝ F = c)
    (e : Basis (Fin c) ℝ F) :
    ∀ᶠ x in l, ∀ (hg : Function.Surjective (L x))
      (ha : finrank ℝ (LinearMap.ker (L x).toLinearMap) = a)
      (b : Basis (Fin a) ℝ (LinearMap.ker (L x).toLinearMap)), (∀ i, (b i : E) = v x i) →
      ∀ ov : Orientation ℝ E (Fin (a + c)),
      (b.orientation = Orientation.shortExactLeft (LinearMap.ker _).subtype_injective
          (LinearMap.exact_subtype_ker_map _) hg ha hc ov e.orientation ↔
        b₀.orientation = Orientation.shortExactLeft (LinearMap.ker _).subtype_injective
          (LinearMap.exact_subtype_ker_map _) hL₀
          ((finrank_eq_card_basis b₀).trans (Fintype.card_fin a)) hc ov e.orientation) := by
  obtain ⟨s, hs⟩ := L₀.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hL₀)
  set S := LinearMap.toContinuousLinearMap s
  have hs₀ (j : Fin c) : L₀.toLinearMap (s (e j)) = e j := by
    simpa using LinearMap.congr_fun hs (e j)
  -- The basis `B₀` of `E` made of `b₀` followed by the lifts `s (e j)` of `e`. Near the limit,
  -- `v x` followed by the same lifts is a basis of the same orientation, and `L x ∘ s` is an
  -- automorphism of `F` of positive determinant, since `L₀ ∘ s` is the identity.
  set B₀ := (Basis.ofExactLift (LinearMap.ker _).subtype_injective
    (LinearMap.exact_subtype_ker_map L₀.toLinearMap) b₀ e (s ∘ e) hs₀).reindex finSumFinEquiv
  have hw : Tendsto (fun x ↦ Fin.append (v x) (s ∘ e)) l (𝓝 ⇑B₀) := by
    rw [Basis.coe_reindex_ofExactLift]
    refine tendsto_pi_nhds.2 fun k ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa using tendsto_pi_nhds.1 hv i
    · simpa using tendsto_const_nhds
  have hM : Tendsto (fun x ↦ ((L x).comp S).det) l (𝓝 1) := by
    have hS : L₀.comp S = ContinuousLinearMap.id ℝ F :=
      ContinuousLinearMap.coe_injective (by simpa [S] using hs)
    have h := (ContinuousLinearMap.continuous_det.tendsto _).comp
      (((ContinuousLinearMap.compL ℝ F E F).flip S).continuous.tendsto L₀ |>.comp hL)
    simpa [Function.comp_def, hS, ContinuousLinearMap.det] using h
  filter_upwards [B₀.eventually_orientation_eq_of_tendsto hw,
    hM.eventually (lt_mem_nhds one_pos)] with x hx hM hg ha b hb ov
  -- The basis `e' = L x ∘ s ∘ e` of `F` has the orientation of `e`, and `s ∘ e` lifts it.
  set φ := LinearMap.equivOfDetNeZero ((L x).comp S).toLinearMap hM.ne'
  have he' : (e.map φ).orientation = e.orientation := by
    rw [Basis.orientation_map, Orientation.map_eq_iff_det_pos _ _ (by rw [Fintype.card_fin, hc])]
    convert hM using 1
    simp [φ, ContinuousLinearMap.det]
  have ht (j : Fin c) : (L x).toLinearMap (s (e j)) = e.map φ j := by simp [φ, S]
  set Bx := (Basis.ofExactLift (LinearMap.ker _).subtype_injective
    (LinearMap.exact_subtype_ker_map (L x).toLinearMap) b (e.map φ) (s ∘ e) ht).reindex
      finSumFinEquiv
  have hx' : Orientation.shortExact (LinearMap.ker _).subtype_injective
      (LinearMap.exact_subtype_ker_map _) hg b.orientation e.orientation ha hc =
        B₀.orientation := by
    rw [← he', Orientation.shortExact_basis_orientation _ _ _ _ _ b _ Bx (fun i ↦ by simp [Bx])
      (fun j ↦ by simp [Bx, ht])]
    refine hx Bx ?_
    rw [Basis.coe_reindex_ofExactLift]
    exact congrArg (Fin.append · _) (funext hb)
  have hx₀ : Orientation.shortExact (LinearMap.ker _).subtype_injective
      (LinearMap.exact_subtype_ker_map _) hL₀ b₀.orientation e.orientation
      ((finrank_eq_card_basis b₀).trans (Fintype.card_fin a)) hc = B₀.orientation :=
    Orientation.shortExact_basis_orientation _ _ _ _ _ b₀ _ B₀ (fun i ↦ by simp [B₀])
      (fun j ↦ by simp [B₀, hs₀])
  rw [eq_comm, Orientation.shortExactLeft_eq_iff, eq_comm (a := b₀.orientation),
    Orientation.shortExactLeft_eq_iff, hx', hx₀]

/-- **The orientations of the kernels of a continuous family of surjections are locally
constant.** Let `L x : E → F` be continuous linear maps between finite-dimensional real normed
spaces, tending along a filter `l` to a surjection `L₀`, and orient each kernel from orientations
`ov` of `E` and `p` of `F`, subspace first (`Orientation.shortExactLeft`): a basis of `ker (L x)`
is positive when, followed by lifts of a `p`-positive basis of `F`, it is `ov`-positive. Let `v x`
be families of vectors of `E` tending to a basis `b₀` of `ker L₀`. Then eventually along `l`, any
basis `b` of `ker (L x)` with vectors `v x` is positive exactly when `b₀` is.

With `l` the neighbourhood filter of a point, this says that the kernel orientation of a continuous
family of surjections is locally constant, read on any continuous family of kernel bases; with `l`
along a sequence, it computes the limit of the kernel orientations from the limiting map `L₀`,
which need not belong to the family. Eventually the maps `L x` are surjective
(`TauCeti.isOpen_setOf_surjective`), so their kernels have the dimension `a`
of `ker L₀`, and vectors `v x` lying in them are eventually linearly independent
(`LinearIndependent.eventually`), hence form such bases. -/
theorem Orientation.eventually_orientation_eq_shortExactLeft_iff_of_tendsto {α : Type*}
    {l : Filter α} {L : α → E →L[ℝ] F} {L₀ : E →L[ℝ] F} (hL : Tendsto L l (𝓝 L₀))
    (hL₀ : Function.Surjective L₀) (b₀ : Basis (Fin a) ℝ (LinearMap.ker L₀.toLinearMap))
    {v : α → Fin a → E} (hv : Tendsto v l (𝓝 fun i ↦ (b₀ i : E))) (hc : finrank ℝ F = c)
    (ov : Orientation ℝ E (Fin (a + c))) (p : Orientation ℝ F (Fin c)) :
    ∀ᶠ x in l, ∀ (hg : Function.Surjective (L x))
      (ha : finrank ℝ (LinearMap.ker (L x).toLinearMap) = a)
      (b : Basis (Fin a) ℝ (LinearMap.ker (L x).toLinearMap)), (∀ i, (b i : E) = v x i) →
      (b.orientation = Orientation.shortExactLeft (LinearMap.ker _).subtype_injective
          (LinearMap.exact_subtype_ker_map _) hg ha hc ov p ↔
        b₀.orientation = Orientation.shortExactLeft (LinearMap.ker _).subtype_injective
          (LinearMap.exact_subtype_ker_map _) hL₀
          ((finrank_eq_card_basis b₀).trans (Fintype.card_fin a)) hc ov p) := by
  set e := finBasisOfFinrankEq ℝ F hc
  filter_upwards [eventually_orientation_eq_shortExactLeft_iff_of_tendsto_basis hL hL₀ b₀ hv hc e]
    with x hx hg ha b hb
  -- Absorb the sign of `p` relative to `e` into the orientation of `E`.
  rcases e.orientation_eq_or_eq_neg p with rfl | rfl
  · exact hx hg ha b hb ov
  · simp only [Orientation.shortExactLeft_neg_right, ← Orientation.shortExactLeft_neg_left]
    exact hx hg ha b hb (-ov)

end Kernel
