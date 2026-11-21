/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.Fiber
public import TauCeti.Geometry.Manifold.Instances.Stiefel.LinearIsometry
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
public import TauCeti.Topology.Homotopy.SerreFibration.Connected
import TauCeti.Geometry.Manifold.Instances.Stiefel.Homogeneous
import TauCeti.Topology.FiberBundle.Empty
import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast
import TauCeti.Topology.Grassmannian.StiefelFibration.Unitary

/-!
# The projection from a Stiefel manifold to the unit sphere

Projecting an orthonormal `(k + 1)`-frame `(p, u₁, …, u_k)` of a real inner product space `E` to
its first vector `p` gives the map `stiefelProj E (k + 1) 0 : V_{k+1}(E) → S(E)` onto the unit
sphere. Its fibre over `p` is the image of `TauCeti.stiefelFrameIncl p k`, so `V_k(p^⊥)` is
homeomorphic to the fibre (`TauCeti.stiefelFrameHomeomorph`), without any dimension assumption on
`E`. For `k = 0`, orthonormal `1`-frames are unit vectors (`TauCeti.stiefelOneHomeomorphSphere`).

When `E` has finite dimension `n + 1`, this projection is locally trivial with fibre the Stiefel
manifold `V_k(ℝⁿ)` (`TauCeti.exists_trivialization_stiefelProj_zero`): in orthonormal coordinates
it is the `O(1 + n)`-equivariant map `V_{k+1}(ℝ^{1+n}) → Sⁿ`, which is locally trivialized by the
Gram–Schmidt local sections of `O(1 + n) → Sⁿ` (`TauCeti.exists_trivialization_unitaryFrameMap`,
`TauCeti.equivariantLocalSectionTrivialization`). For `n < k`, both total space and model fibre are
empty and `Bundle.Trivialization.ofIsEmpty` applies. Consequently:

* in every finite dimension, `V_{k+1}(E) → S(E)` is a Serre fibration
  (`TauCeti.TopCat.mem_serreFibrations_stiefelProj_zero`) and a Hurewicz fibration
  (`TauCeti.isHurewiczFibration_stiefelProj_zero`);
* `V_k(E)` is `(finrank ℝ E - k - 1)`-connected (`TauCeti.subsingleton_homotopyGroup_stiefel`), and
  when `finrank ℝ E = n + 1` and `k ≤ n`, the projection `V_{k+1}(E) → Sⁿ` is `(n - k)`-connected
  (`TauCeti.isNConnected_stiefelProj_zero`).

## Main declarations

* `TauCeti.stiefelOneHomeomorphSphere`: `V₁(E) ≃ₜ S(E)`.
* `TauCeti.exists_trivialization_stiefelProj_zero`: local triviality of `V_{k+1}(E) → S(E)` with
  fibre `V_k(ℝⁿ)` when `finrank ℝ E = n + 1`.
* `TauCeti.TopCat.mem_serreFibrations_stiefelProj_zero`,
  `TauCeti.isHurewiczFibration_stiefelProj_zero`: Serre and Hurewicz fibration properties.
* `TauCeti.subsingleton_homotopyGroup_stiefel`, `TauCeti.pathConnectedSpace_stiefel`,
  `TauCeti.isNConnected_stiefelProj_zero`: connectivity of `V_k(E)` and of `V_{k+1}(E) → Sⁿ`.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§7.7 and 25.6.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 and Example 4.53.
-/

public section

noncomputable section

open Bundle Metric Module Set Topology
open scoped RealInnerProductSpace Topology.Homotopy

namespace TauCeti

/-! ### One-frames and the unit sphere -/

section OneFrame

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthonormal `1`-frame of `E` is the same as a point of the unit sphere of `E`. -/
def stiefelOneHomeomorphSphere : stiefel E 1 ≃ₜ sphere (0 : E) 1 where
  toFun := stiefelProj E 1 0
  invFun p := ⟨fun _ ↦ (p : E), mem_stiefel_iff.2 <| orthonormal_iff_ite.2 fun i j ↦ by
    rw [Subsingleton.elim i j]
    simp [norm_eq_of_mem_sphere p]⟩
  left_inv v := Subtype.ext <| funext fun i ↦ by
    rw [Subsingleton.elim i 0]
    exact coe_stiefelProj 0 v
  right_inv _ := Subtype.ext (by simp)
  continuous_toFun := continuous_stiefelProj 0
  continuous_invFun := (continuous_pi fun _ ↦ continuous_subtypeVal).subtype_mk _

variable {E}

@[simp]
theorem stiefelOneHomeomorphSphere_apply (v : stiefel E 1) :
    stiefelOneHomeomorphSphere E v = stiefelProj E 1 0 v := by
  rw [stiefelOneHomeomorphSphere]
  -- After unfolding `stiefelOneHomeomorphSphere`, `toFun` is `stiefelProj E 1 0`.
  rfl

@[simp]
theorem coe_stiefelOneHomeomorphSphere_symm_apply (p : sphere (0 : E) 1) (i : Fin 1) :
    ((stiefelOneHomeomorphSphere E).symm p : Fin 1 → E) i = p := by
  rw [stiefelOneHomeomorphSphere]
  -- After unfolding `stiefelOneHomeomorphSphere`, `invFun p` is the constant family `p`.
  rfl

@[simp]
theorem stiefelProj_stiefelOneHomeomorphSphere_symm (p : sphere (0 : E) 1) :
    stiefelProj E 1 0 ((stiefelOneHomeomorphSphere E).symm p) = p := by
  rw [← stiefelOneHomeomorphSphere_apply, Homeomorph.apply_symm_apply]

end OneFrame

/-! ### Local triviality in finite dimension -/

section LocallyTrivial

/-- Keeping only the first vector of an orthonormal `(k + 1)`-frame of `ℝ^N`. -/
private def firstOrthonormalFrame {k N : ℕ} (f : finiteOrthonormalFrame ℝ (k + 1) N) :
    finiteOrthonormalFrame ℝ 1 N :=
  ⟨fun _ ↦ f.val 0, f.property.comp _ fun _ _ _ ↦ Subsingleton.elim _ _⟩

private theorem coe_firstOrthonormalFrame {k N : ℕ} (f : finiteOrthonormalFrame ℝ (k + 1) N)
    (i : Fin 1) : (firstOrthonormalFrame f : Fin 1 → Fin N → ℝ) i = f.val 0 :=
  (rfl)

private theorem continuous_firstOrthonormalFrame {k N : ℕ} :
    Continuous (firstOrthonormalFrame (k := k) (N := N)) :=
  continuous_induced_rng.2 <| continuous_pi fun _ ↦ (continuous_apply 0).comp continuous_subtypeVal

private theorem firstOrthonormalFrame_unitaryMap {k N : ℕ} (A : Matrix.unitaryGroup (Fin N) ℝ)
    (f : finiteOrthonormalFrame ℝ (k + 1) N) :
    firstOrthonormalFrame (finiteOrthonormalFrame.unitaryMap A f) =
      finiteOrthonormalFrame.unitaryMap A (firstOrthonormalFrame f) :=
  Subtype.ext <| funext fun _ ↦ by simp [coe_firstOrthonormalFrame]

private theorem firstOrthonormalFrame_standard {k n : ℕ} (hk : k + 1 ≤ 1 + n) :
    firstOrthonormalFrame (finiteOrthonormalFrame.standard ℝ hk) =
      finiteOrthonormalFrame.standard ℝ (Nat.le_add_right 1 n) := by
  refine Subtype.ext <| funext fun i ↦ ?_
  rw [Subsingleton.elim i 0, coe_firstOrthonormalFrame, finiteOrthonormalFrame.coe_standard,
    finiteOrthonormalFrame.coe_standard]
  -- Both `Fin.castLE` maps send `0` to `0 : Fin (1 + n)`.
  exact congrArg (fun j : Fin (1 + n) ↦ Pi.single j (1 : ℝ)) (Fin.ext rfl)

/-- Local triviality of `stiefelProj` on the coordinate model `EuclideanSpace ℝ (Fin (1 + n))`. -/
private theorem exists_trivialization_stiefelProj_euclidean (n k : ℕ)
    (q : sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1) :
    ∃ e : Trivialization (stiefel (EuclideanSpace ℝ (Fin n)) k)
      (stiefelProj (EuclideanSpace ℝ (Fin (1 + n))) (k + 1) 0), q ∈ e.baseSet := by
  set V := EuclideanSpace ℝ (Fin (1 + n))
  by_cases hk : k ≤ n
  · -- Trivialize the `O(1 + n)`-equivariant frame map by a Gram–Schmidt local section on `Sⁿ`.
    let _ := finiteOrthonormalFrame.unitaryMulAction ℝ (k + 1) (1 + n)
    let _ := finiteOrthonormalFrame.unitaryMulAction ℝ 1 (1 + n)
    have : ContinuousSMul (Matrix.unitaryGroup (Fin (1 + n)) ℝ)
        (finiteOrthonormalFrame ℝ (k + 1) (1 + n)) :=
      ⟨finiteOrthonormalFrame.continuous_unitaryMap⟩
    let φ₁ := finiteOrthonormalFrame.sphereHomeomorph (1 + n)
    let φk := stiefel.finiteOrthonormalFrameHomeomorph (k + 1) (1 + n)
    obtain ⟨c, hcq⟩ := exists_trivialization_unitaryFrameMap (𝕜 := ℝ) (r := 1) (m := n) (φ₁.symm q)
    let f₀ := finiteOrthonormalFrame.standard ℝ (Nat.le_add_right 1 n)
    have hk' : k + 1 ≤ 1 + n := by omega
    let e₀ := equivariantLocalSectionTrivialization
      (firstOrthonormalFrame (k := k) (N := 1 + n)) continuous_firstOrthonormalFrame
      firstOrthonormalFrame_unitaryMap f₀
      ⟨finiteOrthonormalFrame.standard ℝ hk', firstOrthonormalFrame_standard hk'⟩
      c.baseSet c.open_baseSet (fun f ↦ c.toOpenPartialHomeomorph.symm (f, 1))
      c.continuousOn_symm_prodMk_left fun f hf ↦ by
        -- Unfold the local `unitaryMulAction` scalar multiplication to `unitaryMap`.
        change finiteOrthonormalFrame.unitaryMap (c.toOpenPartialHomeomorph.symm (f, 1)) f₀ = f
        rw [show f₀ = unitaryFrameMap 1 n 1 from unitaryFrameMap_one.symm, ← unitaryFrameMap_mul,
          mul_one]
        exact c.proj_symm_apply' hf
    -- Transport the fibre over `q₀ = φ₁ f₀` to `V_k(ℝⁿ)` via `stiefelFrameHomeomorph`.
    have hcomp : (φ₁ ∘ firstOrthonormalFrame ∘ φk) = stiefelProj V (k + 1) 0 := by
      ext v : 1
      exact Subtype.ext (by simp [φ₁, φk, coe_firstOrthonormalFrame])
    let q₀ : sphere (0 : V) 1 := φ₁ f₀
    let hFib₁ : {f : finiteOrthonormalFrame ℝ (k + 1) (1 + n) // firstOrthonormalFrame f = f₀} ≃ₜ
        stiefelProj V (k + 1) 0 ⁻¹' {q₀} :=
      φk.symm.subtype fun v ↦ by
        rw [mem_preimage, mem_singleton_iff, ← hcomp]
        simp only [Function.comp_apply, Homeomorph.apply_symm_apply, q₀, φ₁.injective.eq_iff]
    have : Fact (finrank ℝ V = n + 1) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
    have hperp : finrank ℝ (ℝ ∙ (q₀ : V))ᗮ = n :=
      Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere q₀)
    let Lperp : (ℝ ∙ (q₀ : V))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((stdOrthonormalBasis ℝ (ℝ ∙ (q₀ : V))ᗮ).reindex (finCongr hperp)).repr
    let hFib := hFib₁.trans ((stiefelFrameHomeomorph q₀ k).symm.trans (Lperp.stiefelHomeomorph k))
    let e₁ := ((e₀.compHomeomorph φk).homeomorphComp φ₁).transFiberHomeomorph hFib
    rw [← hcomp]
    refine ⟨e₁, ?_⟩
    simpa [e₁, Trivialization.transFiberHomeomorph, Trivialization.homeomorphComp,
      Trivialization.compHomeomorph, e₀, equivariantLocalSectionTrivialization_baseSet] using hcq
  · have : IsEmpty (stiefel V (k + 1)) :=
      ⟨fun v ↦ absurd ((nonempty_stiefel (E := V) (k := k + 1)).1 ⟨v.val, v.property⟩)
        (by rw [finrank_euclideanSpace_fin]; omega)⟩
    have : IsEmpty (stiefel (EuclideanSpace ℝ (Fin n)) k) :=
      ⟨fun v ↦ absurd
        ((nonempty_stiefel (E := EuclideanSpace ℝ (Fin n)) (k := k)).1 ⟨v.val, v.property⟩)
        (by rw [finrank_euclideanSpace_fin]; omega)⟩
    exact ⟨Trivialization.ofIsEmpty _ _, by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Stiefel sphere projection is locally trivial.** If `E` has dimension `n + 1`, every point
of the unit sphere of `E` lies in the base set of a chart of
`stiefelProj E (k + 1) 0 : V_{k+1}(E) → S(E)` with fibre `V_k(ℝⁿ)`. -/
theorem exists_trivialization_stiefelProj_zero {n : ℕ} (hE : finrank ℝ E = n + 1) (k : ℕ)
    (p : sphere (0 : E) 1) :
    ∃ e : Trivialization (stiefel (EuclideanSpace ℝ (Fin n)) k) (stiefelProj E (k + 1) 0),
      p ∈ e.baseSet := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  let L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (1 + n)) :=
    ((stdOrthonormalBasis ℝ E).reindex (finCongr (by omega : finrank ℝ E = 1 + n))).repr
  obtain ⟨e₀, he₀⟩ := exists_trivialization_stiefelProj_euclidean n k (L.unitSphereIsometryEquiv p)
  have hcomp : (L.unitSphereIsometryEquiv.toHomeomorph.symm ∘
      stiefelProj (EuclideanSpace ℝ (Fin (1 + n))) (k + 1) 0 ∘ L.stiefelHomeomorph (k + 1)) =
      stiefelProj E (k + 1) 0 := by
    ext v : 1
    rw [Function.comp_apply, Function.comp_apply, L.stiefelProj_stiefelHomeomorph]
    exact L.unitSphereIsometryEquiv.symm_apply_apply _
  rw [← hcomp]
  refine ⟨(e₀.compHomeomorph (L.stiefelHomeomorph (k + 1))).homeomorphComp
    L.unitSphereIsometryEquiv.toHomeomorph.symm, ?_⟩
  simpa [Trivialization.homeomorphComp, Trivialization.compHomeomorph] using he₀

variable (E) in
/-- **The Stiefel sphere projection is a Serre fibration** in every finite dimension. -/
theorem TopCat.mem_serreFibrations_stiefelProj_zero [FiniteDimensional ℝ E] (k : ℕ) :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨stiefelProj E (k + 1) 0, continuous_stiefelProj 0⟩ :
        _root_.TopCat.of (stiefel E (k + 1)) ⟶ _root_.TopCat.of (sphere (0 : E) 1)) := by
  rcases eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    exact TopCat.mem_serreFibrations_of_exists_trivialization (F := Empty) fun p ↦ isEmptyElim p
  · exact TopCat.mem_serreFibrations_of_exists_trivialization
      (exists_trivialization_stiefelProj_zero (Nat.sub_add_cancel hpos).symm k)

variable (E) in
/-- **The Stiefel sphere projection is a Hurewicz fibration** in every finite dimension. -/
theorem isHurewiczFibration_stiefelProj_zero.{v} [FiniteDimensional ℝ E] (k : ℕ) :
    IsHurewiczFibration.{v} (stiefelProj E (k + 1) 0) := by
  rcases eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    exact isHurewiczFibration_of_exists_trivialization (F := Empty) fun p ↦ isEmptyElim p
  · exact isHurewiczFibration_of_exists_trivialization
      (exists_trivialization_stiefelProj_zero (Nat.sub_add_cancel hpos).symm k)

end LocallyTrivial

/-! ### Connectivity -/

section Connectivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Connectivity of Stiefel manifolds.** For a finite-dimensional real inner product space `E`,
the Stiefel manifold `V_k(E)` is `(finrank ℝ E - k - 1)`-connected: its homotopy group indexed by
a finite type `M` is trivial whenever `Nat.card M + k < finrank ℝ E`. -/
theorem subsingleton_homotopyGroup_stiefel [FiniteDimensional ℝ E] {M : Type*} [Finite M] {k : ℕ}
    (h : Nat.card M + k < finrank ℝ E) (v : stiefel E k) :
    Subsingleton (HomotopyGroup M (stiefel E k) v) := by
  let L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) := (stdOrthonormalBasis ℝ E).repr
  let φ : stiefel E k ≃ₜ finiteOrthonormalFrame ℝ k (finrank ℝ E) :=
    (L.stiefelHomeomorph k).trans (stiefel.finiteOrthonormalFrameHomeomorph k (finrank ℝ E))
  have := finiteOrthonormalFrame.subsingleton_homotopyGroup h (φ v)
  exact (HomotopyGroup.homeomorphEquiv φ v).subsingleton

/-- For `k < finrank ℝ E`, the Stiefel manifold `V_k(E)` is path-connected. -/
theorem pathConnectedSpace_stiefel [FiniteDimensional ℝ E] {k : ℕ} (h : k < finrank ℝ E) :
    PathConnectedSpace (stiefel E k) := by
  obtain ⟨v, hv⟩ := (nonempty_stiefel (E := E) (k := k)).2 h.le
  exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero ⟨v, hv⟩).2
    (subsingleton_homotopyGroup_stiefel (by simpa using h) ⟨v, hv⟩)

/-- **Connectivity of the Stiefel sphere projection.** When `finrank ℝ E = n + 1` and `k ≤ n`,
the projection `V_{k+1}(E) → Sⁿ` to the first vector is `(n - k)`-connected: its fibres `V_k(p^⊥)`
are nonempty and `(n - k - 1)`-connected. -/
theorem isNConnected_stiefelProj_zero {n k : ℕ} (hE : finrank ℝ E = n + 1) (hk : k ≤ n) :
    (⟨stiefelProj E (k + 1) 0, continuous_stiefelProj 0⟩ :
      C(stiefel E (k + 1), sphere (0 : E) 1)).IsNConnected (n - k) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ E = n + 1) := ⟨hE⟩
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_stiefelProj_zero E k) (n - k)).2 fun p ↦ ?_
  have hperp : finrank ℝ (ℝ ∙ (p : E))ᗮ = n :=
    Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
  refine ⟨?_, fun e m hm ↦ ?_⟩
  · obtain ⟨x, hx⟩ := (nonempty_stiefel (E := (ℝ ∙ (p : E))ᗮ) (k := k)).2 (by omega)
    exact ⟨stiefelFrameHomeomorph p k ⟨x, hx⟩⟩
  · let φ : (_root_.TopCat.ofHom ⟨stiefelProj E (k + 1) 0, continuous_stiefelProj 0⟩ :
        _root_.TopCat.of (stiefel E (k + 1)) ⟶ _root_.TopCat.of (sphere (0 : E) 1)).fiber p ≃ₜ
        stiefel (ℝ ∙ (p : E))ᗮ k :=
      ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (stiefelFrameHomeomorph p k).symm
    have := subsingleton_homotopyGroup_stiefel (M := Fin m) (by simp [hperp]; omega) (φ e)
    exact (HomotopyGroup.homeomorphEquiv φ e).subsingleton

end Connectivity

end TauCeti
