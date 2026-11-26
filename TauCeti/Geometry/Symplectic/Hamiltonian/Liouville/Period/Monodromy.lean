/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Fibration
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Compact
public import TauCeti.Topology.VectorBundle.Lattice
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# The linear monodromy of the period lattice

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
onto a boundaryless Hausdorff manifold `B` of dimension `n`, with period lattices
`Λ_b ⊆ T*_b B` (`IsLagrangianTorusFibration.periodLattice`). The covectors lying in the period
lattices form the **period lattice bundle** `Λ ⊆ T*B`, the domain of `TauCeti.latticeProj` for
the family `b ↦ Λ_b`; its fibrewise quotient `T*B/Λ` is the torus bundle associated with the
fibration.

Near every point of `B` there are action coordinates `a : B → ℝⁿ` with
`Λ_b = 2π (ℤ da₁(b) + ⋯ + ℤ daₙ(b))`
(`IsLagrangianTorusFibration.exists_periodLattice_eq_closure_mvfderiv`).
Their differentials are continuous covector fields, linearly independent because `Λ_b` is a full
lattice. So the period lattice bundle is a covering space of `B`
(`IsLagrangianTorusFibration.isCoveringMap_latticeProj_periodLattice`), by the general
`TauCeti.isCoveringMap_latticeProj`. Lifting paths to this covering transports periods along paths
in `B`: a homotopy class of paths from `x` to `y` gives a group isomorphism `Λ_x ≃+ Λ_y`
(`TauCeti.latticeMonodromy`), and loops at `x` give the **linear monodromy** of the fibration, the
representation `π₁(B, x) → GL(Λ_x) ≅ GL(n, ℤ)` (`TauCeti.latticeMonodromyHom`).

Transport follows differentials of functions which are periods: if `dg_b ∈ Λ_b` for `b` in a set
`U` on which `g` is `C¹`, then transport along a path in `U` carries `dg_x` to `dg_y`
(`IsLagrangianTorusFibration.latticeMonodromy_mk_mvfderiv`). Hence a fibration admitting global
action coordinates, whose period lattice is spanned over `ℤ` at every point by the differentials of
`C¹` functions on all of `B`, has trivial linear monodromy
(`IsLagrangianTorusFibration.latticeMonodromyHom_eq_one_of_periodLattice_eq_closure_mvfderiv`).
So nontrivial linear monodromy is an obstruction to global action coordinates.

Conversely, over a connected base, trivial linear monodromy gives a global frame of the period
lattice. A continuous covector field whose values are periods is locally exact: near every point
it is the differential of a smooth function
(`IsLagrangianTorusFibration.exists_contMDiffOn_eq_mvfderiv_of_continuous`). The proof takes an
integer combination of `2π` times local action coordinates, using that two continuous lifts of a
connected open set to the period lattice bundle which agree at one point agree everywhere.
Trivial monodromy lifts the identity of `B` to continuous sections of periods through a basis of
one period lattice, which span every period lattice
(`TauCeti.exists_frame_of_latticeMonodromyHom_eq_one`). So they are closed one-forms
`α_1, …, α_n` forming a smooth frame of `T*B` with `Λ_b = ℤ α_1(b) + ⋯ + ℤ α_n(b)` for every `b`
(`IsLagrangianTorusFibration.exists_periodLattice_eq_closure_of_latticeMonodromyHom_eq_one`), the
global frame which identifies a fibration with a Lagrangian section with its model `T*B/Λ`
(`IsLagrangianTorusFibration.exists_lagrangian_section_iff`). Hence the linear monodromy is trivial
exactly when the period lattice has a global frame
(`IsLagrangianTorusFibration.latticeMonodromyHom_eq_one_iff_exists_periodLattice_eq_closure`).

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (the period lattice bundle and its monodromy).
-/

public section

open Bundle (TotalSpace)
open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

variable (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed)

/-- **The period lattice bundle is a covering space of the base.** The covectors of `T*B` lying
in the period lattices of a regular Lagrangian torus fibration form a covering space of `B`:
near every point, the integer coordinates in the frame `2π da₁, …, 2π daₙ` of local action
coordinates `a` identify it with the product of a neighbourhood and `ℤⁿ`. -/
theorem isCoveringMap_latticeProj_periodLattice [BoundarylessManifold J B] :
    IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc)) := by
  refine isCoveringMap_latticeProj _ (ι := Fin (finrank ℝ F))
    (by rw [Fintype.card_fin, ContinuousLinearMap.dual_finrank_eq]) fun b₀ ↦ ?_
  obtain ⟨a, V, hV, hb₀, -, hloc, hΛ⟩ := h.exists_periodLattice_eq_closure_mvfderiv hσc b₀
  refine ⟨fun i b ↦ (2 * Real.pi) • mvfderiv J (fun c ↦ a c i) b, V, hV, hb₀,
    fun i b hb ↦ ?_, fun b hb ↦ ⟨?_, hΛ b hb⟩⟩
  · have hai : ContMDiffAt J 𝓘(ℝ) (0 + 1) (fun c ↦ a c i) b :=
      ((contMDiffAt_pi_module_iff.1 (hloc b hb).contMDiffAt) i).of_le (by simp)
    exact (continuousAt_const.smul_section
      hai.contMDiffAt_totalSpaceMk_mvfderiv.continuousAt).continuousWithinAt
  · exact h.linearIndependent_of_periodLattice_le_closure hσc (by simp) (hΛ b hb).le

variable {U : Set B} {g : B → ℝ}

/-- **Transport of periods follows differentials.** Let `g` be a function on the base which is
`C¹` at every point of a set `U`, and whose differential `dg_b` is a period at every `b ∈ U`, such
as `2π` times an action coordinate. Then transporting periods along a path `γ` in `U` carries
`dg` at the start of `γ` to `dg` at its end. -/
theorem latticeMonodromy_mk_mvfderiv
    (hL : IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc)))
    (hg : ∀ b ∈ U, ContMDiffAt J 𝓘(ℝ) 1 g b)
    (hgΛ : ∀ b ∈ U, mvfderiv J g b ∈ h.periodLattice hσc b) {x y : B} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ U) :
    latticeMonodromy hL (.mk γ) ⟨mvfderiv J g x, hgΛ x (γ.source ▸ hγ 0)⟩ =
      ⟨mvfderiv J g y, hgΛ y (γ.target ▸ hγ 1)⟩ :=
  latticeMonodromy_mk_of_continuousOn hL
    (fun b hb ↦ ((zero_add (1 : WithTop ℕ∞)).symm ▸ hg b hb :
      ContMDiffAt J 𝓘(ℝ) (0 + 1) g b).contMDiffAt_totalSpaceMk_mvfderiv.continuousAt
      |>.continuousWithinAt) hgΛ γ hγ

/-- **Global action coordinates force trivial monodromy.** If the period lattice of a regular
Lagrangian torus fibration is spanned over `ℤ` at every point of the base by the differentials of
finitely many `C¹` functions on the whole base, such as `2π` times global action coordinates, then
its linear monodromy is trivial. -/
theorem latticeMonodromyHom_eq_one_of_periodLattice_eq_closure_mvfderiv {ι : Type*} [Finite ι]
    (hL : IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc)))
    {g : ι → B → ℝ} (hg : ∀ i, ContMDiff J 𝓘(ℝ) 1 (g i))
    (hΛ : ∀ b, h.periodLattice hσc b = AddSubgroup.closure (range fun i ↦ mvfderiv J (g i) b))
    (x : B) : latticeMonodromyHom hL x = 1 :=
  latticeMonodromyHom_eq_one hL
    (fun i ↦ ((zero_add (1 : WithTop ℕ∞)).symm ▸ hg i :
      ContMDiff J 𝓘(ℝ) (0 + 1) (g i)).contMDiff_totalSpaceMk_mvfderiv.continuous) hΛ x

/-- **Continuous sections of periods are locally exact.** A continuous covector field `s` on the
base of a regular Lagrangian torus fibration whose values are periods is, near every point, the
differential of a smooth function. -/
theorem exists_contMDiffOn_eq_mvfderiv_of_continuous [BoundarylessManifold J B]
    {s : ∀ b, TangentSpace J b →L[ℝ] ℝ}
    (hs : Continuous fun b ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
      (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ) b (s b))
    (hsΛ : ∀ b, s b ∈ h.periodLattice hσc b) (b₀ : B) :
    ∃ g : B → ℝ, ∃ U, IsOpen U ∧ b₀ ∈ U ∧ ContMDiffOn J 𝓘(ℝ) ∞ g U ∧
      ∀ b ∈ U, s b = mvfderiv J g b := by
  have := J.locallyPathConnectedSpace_of_chartedSpace B
  obtain ⟨a, V, hV, hb₀, -, hlocd, hΛ⟩ := h.exists_periodLattice_eq_closure_mvfderiv hσc b₀
  have ha (b : B) (hb : b ∈ V) : ContMDiffAt J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ a b :=
    (hlocd b hb).contMDiffAt
  obtain ⟨k, hk⟩ := AddSubgroup.mem_closure_range_iff_of_fintype.1
    ((hΛ b₀ hb₀).le (hsΛ b₀))
  set ℓ : (Fin (finrank ℝ F) → ℝ) →L[ℝ] ℝ :=
    (2 * Real.pi) • ∑ j, (k j : ℝ) • ContinuousLinearMap.proj j
  -- On `V`, the differential of `ℓ ∘ a` is the integer combination of the periods `2π da_j`.
  have hdg (b : B) (hb : b ∈ V) : mvfderiv J (ℓ ∘ a) b =
      ∑ j, k j • ((2 * Real.pi) • mvfderiv J (fun c ↦ a c j) b) := by
    have hab := (ha b hb).mdifferentiableAt (by simp)
    have hj (j : Fin (finrank ℝ F)) (v : TangentSpace J b) :
        mvfderiv J (fun c ↦ a c j) b v = mvfderiv J a b v j :=
      (mvfderiv_apply_apply hab v j).symm
    ext v
    rw [ℓ.mvfderiv_comp_apply hab]
    simp only [ℓ, hj, smul_apply, FunLike.coe_sum,
      Finset.sum_apply, ContinuousLinearMap.proj_apply, ← Int.cast_smul_eq_zsmul ℝ,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hdgΛ (b : B) (hb : b ∈ V) : mvfderiv J (ℓ ∘ a) b ∈ h.periodLattice hσc b := by
    rw [hdg b hb, hΛ b hb]
    exact AddSubgroup.sum_mem _ fun j _ ↦
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (mem_range_self j)) _
  -- On the connected component `W` of `b₀` in `V`, the continuous sections of periods `s` and
  -- `d(ℓ ∘ a)` agree at `b₀`, hence everywhere.
  set W := connectedComponentIn V b₀
  have hWV : W ⊆ V := connectedComponentIn_subset V b₀
  have hcont : ContinuousOn (fun b ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
      (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ) b (mvfderiv J (ℓ ∘ a) b)) V := fun b hb ↦
    ((ℓ.contMDiff.contMDiffAt.comp b (ha b hb)).of_le (by simp) :
      ContMDiffAt J 𝓘(ℝ) (0 + 1) (ℓ ∘ a) b).contMDiffAt_totalSpaceMk_mvfderiv.continuousAt
      |>.continuousWithinAt
  refine ⟨ℓ ∘ a, W, hV.connectedComponentIn, mem_connectedComponentIn hb₀, fun b hb ↦
    (ℓ.contMDiff.contMDiffAt.comp b (ha b (hWV hb))).contMDiffWithinAt, ?_⟩
  exact eqOn_of_continuousOn_of_mem_lattice (h.isCoveringMap_latticeProj_periodLattice hσc)
    isPreconnected_connectedComponentIn hs.continuousOn (hcont.mono hWV) (fun b _ ↦ hsΛ b)
    (fun b hb ↦ hdgΛ b (hWV hb)) (mem_connectedComponentIn hb₀) (hk.trans (hdg b₀ hb₀).symm)

/-- **Trivial linear monodromy gives a global frame of period one-forms.** Let the base `B` of a
regular Lagrangian torus fibration be connected, and let its linear monodromy at some point be
trivial. Then there are closed one-forms `α_1, …, α_n` on `B`, `n = dim B`, forming a smooth frame
of `T*B`, which span the period lattice over `ℤ` at every point:
`Λ_b = ℤ α_1(b) + ⋯ + ℤ α_n(b)`. -/
theorem exists_periodLattice_eq_closure_of_latticeMonodromyHom_eq_one [BoundarylessManifold J B]
    [PreconnectedSpace B]
    (hL : IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc))) {x : B} (hx : latticeMonodromyHom hL x = 1) :
    ∃ α : Fin (finrank ℝ F) → SmoothForm J B ℝ 1, (∀ i, (α i).IsClosed) ∧
      IsLocalFrameOn J (F →L[ℝ] ℝ) ∞ (fun i b ↦ SmoothForm.degreeOneEquiv (α i) b) univ ∧
      ∀ b, h.periodLattice hσc b =
        AddSubgroup.closure (range fun i ↦ (SmoothForm.degreeOneEquiv (α i) b : F →L[ℝ] ℝ)) := by
  set n := finrank ℝ F
  have : Nonempty B := ⟨x⟩
  have := J.locallyPathConnectedSpace_of_chartedSpace B
  have := J.pathConnectedSpace B
  -- Every period lattice is a full lattice, spanned by `2π` times differentials of actions.
  have hLb (b : B) : ∃ t : Fin n → TangentSpace J b →L[ℝ] ℝ,
      LinearIndependent ℝ t ∧ h.periodLattice hσc b = AddSubgroup.closure (range t) := by
    obtain ⟨a, V, -, hb, -, -, hΛ⟩ := h.exists_periodLattice_eq_closure_mvfderiv hσc b
    exact ⟨_, h.linearIndependent_of_periodLattice_le_closure hσc (by simp [n]) (hΛ b hb).le,
      hΛ b hb⟩
  obtain ⟨s, hs, hsL⟩ := TauCeti.exists_frame_of_latticeMonodromyHom_eq_one hL hLb hx
  have hsmem (i : Fin n) (b : B) : s i b ∈ h.periodLattice hσc b :=
    (hsL b).2 ▸ AddSubgroup.subset_closure ⟨i, rfl⟩
  have hloc (i : Fin n) (b₀ : B) := h.exists_contMDiffOn_eq_mvfderiv_of_continuous hσc (hs i)
    (hsmem i) b₀
  -- So each `s i` is smooth.
  have hsmooth (i : Fin n) : ContMDiff J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ (fun b ↦ TotalSpace.mk'
      (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ) b (s i b)) := fun b₀ ↦ by
    obtain ⟨g, U, hU, hb₀, hg, hgs⟩ := hloc i b₀
    have hg' : ContMDiffAt J 𝓘(ℝ) (∞ + 1) g b₀ :=
      ((hg b₀ hb₀).contMDiffAt (hU.mem_nhds hb₀)).of_le (by simp)
    refine hg'.contMDiffAt_totalSpaceMk_mvfderiv.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hb₀] with b hb
    rw [hgs b hb]
  set α : Fin n → SmoothForm J B ℝ 1 := fun i ↦ SmoothForm.degreeOneEquiv.symm ⟨s i, hsmooth i⟩
  have hα (i : Fin n) (b : B) : SmoothForm.degreeOneEquiv (α i) b = s i b := by simp [α]
  have hli (b : B) : LinearIndependent ℝ fun i ↦ SmoothForm.degreeOneEquiv (α i) b := by
    simpa only [hα] using (hsL b).1
  refine ⟨α, fun i ↦ ?_, .of_linearIndependent_of_card_eq_finrank
    (by simp [n, ContinuousLinearMap.dual_finrank_eq])
    (fun i ↦ (SmoothForm.degreeOneEquiv (α i)).contMDiff.contMDiffOn) fun b _ ↦ hli b,
    fun b ↦ ?_⟩
  · -- `α i` has the local primitives `g`.
    refine (SmoothForm.isClosed_def _).2 (mextDeriv_eq_zero_of_forall_exists_isPrimitiveOn
      fun b₀ ↦ ?_)
    obtain ⟨g, U, hU, hb₀, hg, hgs⟩ := hloc i b₀
    refine ⟨g, U, hb₀, ⟨hU, hg.mdifferentiableOn (by simp), fun b hb ↦ ?_⟩, hg.of_le (by simp)⟩
    rw [mextDeriv_ofFunction, ← hgs b hb]
    exact ContinuousAlternatingMap.ext fun v ↦ by simp [α]
  · have hb := (hsL b).2
    simp only [← hα] at hb
    exact hb

/-- **The linear monodromy is trivial exactly when the period lattice has a global frame.** Over a
connected base, the linear monodromy of a regular Lagrangian torus fibration at a point is trivial
if and only if there are closed one-forms `α_1, …, α_n`, `n = dim B`, forming a smooth frame of
`T*B` and spanning the period lattice over `ℤ` at every point. -/
theorem latticeMonodromyHom_eq_one_iff_exists_periodLattice_eq_closure [BoundarylessManifold J B]
    [PreconnectedSpace B]
    (hL : IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc))) (x : B) :
    latticeMonodromyHom hL x = 1 ↔ ∃ α : Fin (finrank ℝ F) → SmoothForm J B ℝ 1,
      (∀ i, (α i).IsClosed) ∧
        IsLocalFrameOn J (F →L[ℝ] ℝ) ∞ (fun i b ↦ SmoothForm.degreeOneEquiv (α i) b) univ ∧
        ∀ b, h.periodLattice hσc b =
          AddSubgroup.closure (range fun i ↦ (SmoothForm.degreeOneEquiv (α i) b : F →L[ℝ] ℝ)) :=
  ⟨fun hx ↦ h.exists_periodLattice_eq_closure_of_latticeMonodromyHom_eq_one hσc hL hx,
    fun ⟨α, _, _, hΛ⟩ ↦ latticeMonodromyHom_eq_one hL
      (fun i ↦ (SmoothForm.degreeOneEquiv (α i)).contMDiff.continuous) hΛ x⟩

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
