/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Orthonormal

/-!
# Forgetting the last vector of an orthonormal frame

The map `finiteOrthonormalFrame.forgetLast` deletes the last vector of an ordered
orthonormal frame. Its fibre over `f` is homeomorphic to the unit sphere in the
orthogonal complement of the span of `f`, by reading the last vector. The inverse
appends that vector, retaining the order of all the original vectors.

`forgetLastFiberSphere` identifies this fibre with the unit sphere in a coordinate
space of dimension `N - r`. In particular, over the reals the fibre of
`V_(r+1)(ℝ^N) → V_r(ℝ^N)` is `S^(N-r-1)` when `r < N`. The complement-sphere
description also applies in rank zero and when there is no room for another vector;
in the latter case the sphere and the fibre are empty. This is the fibre comparison
used in the sphere-fibration tower of Stiefel spaces. Local triviality and homotopy
group calculations are not asserted here.

## References

* A. Hatcher, *Algebraic Topology*, §4.2 (Stiefel manifolds and their sphere fibres).
-/

public noncomputable section

open Set Topology InnerProductSpace

namespace TauCeti.finiteOrthonormalFrame

variable {𝕜 : Type*} [RCLike 𝕜] {r N : ℕ}

/-- Delete the last vector, keeping the first `r` vectors in their given order. -/
def forgetLast (f : finiteOrthonormalFrame 𝕜 (r + 1) N) :
    finiteOrthonormalFrame 𝕜 r N :=
  ⟨fun i ↦ f.1 i.castSucc, f.2.comp _ (Fin.castSucc_injective r)⟩

@[simp] theorem forgetLast_apply (f : finiteOrthonormalFrame 𝕜 (r + 1) N) (i : Fin r) :
    (forgetLast f).1 i = f.1 i.castSucc := (rfl)

@[fun_prop] theorem continuous_forgetLast :
    Continuous (forgetLast : finiteOrthonormalFrame 𝕜 (r + 1) N → _) :=
  (continuous_pi fun i ↦ (continuous_apply i.castSucc).comp continuous_subtype_val).subtype_mk _

/-- Forgetting the last vector commutes with the ambient unitary action. -/
@[simp] theorem forgetLast_unitaryMap (A : Matrix.unitaryGroup (Fin N) 𝕜)
    (f : finiteOrthonormalFrame 𝕜 (r + 1) N) :
    forgetLast (unitaryMap A f) = unitaryMap A (forgetLast f) := by
  apply Subtype.ext
  funext i
  simp

/-- The Euclidean orthogonal complement of the span of a frame. -/
def complement (f : finiteOrthonormalFrame 𝕜 r N) : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin N)) :=
  (Submodule.span 𝕜 (range fun i ↦ (WithLp.toLp 2 (f.1 i) : EuclideanSpace 𝕜 (Fin N))))ᗮ

/-- Membership in the complement means orthogonality to every vector of the frame. -/
@[simp] theorem mem_complement (f : finiteOrthonormalFrame 𝕜 r N)
    (v : EuclideanSpace 𝕜 (Fin N)) :
    v ∈ f.complement ↔ ∀ i, inner 𝕜 (WithLp.toLp 2 (f.1 i)) v = 0 := by
  rw [complement, Submodule.mem_orthogonal]
  simpa only [Submodule.mem_orthogonalBilin, Set.forall_mem_range, innerₛₗ_apply_apply] using
    (Submodule.mem_orthogonalBilin_span (B := innerₛₗ 𝕜) (y := v)
      (s := range fun i ↦ (WithLp.toLp 2 (f.1 i) : EuclideanSpace 𝕜 (Fin N))))

/-- The complement has the dimension left over after the frame vectors are removed. -/
@[simp] theorem finrank_complement (f : finiteOrthonormalFrame 𝕜 r N) :
    Module.finrank 𝕜 f.complement = N - r := by
  have h := Submodule.finrank_add_finrank_orthogonal (Submodule.span 𝕜
    (range fun i ↦ (WithLp.toLp 2 (f.1 i) : EuclideanSpace 𝕜 (Fin N))))
  rw [finrank_span_eq_card f.2.linearIndependent, Fintype.card_fin,
    finrank_euclideanSpace, Fintype.card_fin] at h
  dsimp [complement]
  exact Nat.eq_sub_of_add_eq' h

/-- Append a unit vector perpendicular to the frame as its new last vector. -/
def snoc (f : finiteOrthonormalFrame 𝕜 r N) (v : Metric.sphere (0 : f.complement) 1) :
    finiteOrthonormalFrame 𝕜 (r + 1) N :=
  ⟨Fin.snoc f.1 (WithLp.ofLp v.1.1), by
    classical
    have hv : ‖(v.1.1 : EuclideanSpace 𝕜 (Fin N))‖ = 1 :=
      mem_sphere_zero_iff_norm.1 v.2
    have ho := (mem_complement f v.1.1).1 v.1.2
    refine orthonormal_iff_ite.2 fun i j ↦ ?_
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp [inner_self_eq_norm_sq_to_K, hv]
    · simpa [(Fin.castSucc_ne_last j).symm] using (inner_eq_zero_symm.2 (ho j))
    · simpa using ho i
    · simpa using orthonormal_iff_ite.1 f.2 i j⟩

@[simp] theorem snoc_castSucc (f : finiteOrthonormalFrame 𝕜 r N)
    (v : Metric.sphere (0 : f.complement) 1) (i : Fin r) :
    (f.snoc v).1 i.castSucc = f.1 i := by simp [snoc]

@[simp] theorem snoc_last (f : finiteOrthonormalFrame 𝕜 r N)
    (v : Metric.sphere (0 : f.complement) 1) :
    (f.snoc v).1 (Fin.last r) = WithLp.ofLp v.1.1 := by simp [snoc]

@[simp] theorem forgetLast_snoc (f : finiteOrthonormalFrame 𝕜 r N)
    (v : Metric.sphere (0 : f.complement) 1) : forgetLast (f.snoc v) = f := by
  ext i k
  simp

/-- Appending a perpendicular unit vector is continuous. -/
@[fun_prop] theorem continuous_snoc (f : finiteOrthonormalFrame 𝕜 r N) :
    Continuous f.snoc := by
  refine (continuous_pi fun i ↦ ?_).subtype_mk _
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp only [Fin.snoc_last]
    fun_prop
  · simpa only [snoc, Fin.snoc_castSucc] using
      (continuous_const : Continuous (fun _ : Metric.sphere (0 : f.complement) 1 ↦ f.1 i))

/-- The last vector of a frame in the fibre, as a unit vector in the complement. -/
def lastVector (f : finiteOrthonormalFrame 𝕜 r N)
    (g : {g : finiteOrthonormalFrame 𝕜 (r + 1) N // forgetLast g = f}) :
    Metric.sphere (0 : f.complement) 1 :=
  ⟨⟨WithLp.toLp 2 (g.1.1 (Fin.last r)), by
    apply (mem_complement f _).2
    intro i
    have hi := congrArg (fun h : finiteOrthonormalFrame 𝕜 r N ↦ h.1 i) g.2
    rw [← hi, forgetLast_apply]
    exact g.1.2.2 (Fin.castSucc_ne_last i)⟩,
    mem_sphere_zero_iff_norm.2 (g.1.2.1 (Fin.last r))⟩

@[simp] theorem coe_lastVector (f : finiteOrthonormalFrame 𝕜 r N)
    (g : {g : finiteOrthonormalFrame 𝕜 (r + 1) N // forgetLast g = f}) :
    ((f.lastVector g).1 : EuclideanSpace 𝕜 (Fin N)) =
      WithLp.toLp 2 (g.1.1 (Fin.last r)) := (rfl)

/-- Reading the last vector identifies a forgetful fibre with the complement's unit sphere. -/
def forgetLastFiberHomeomorph (f : finiteOrthonormalFrame 𝕜 r N) :
    {g : finiteOrthonormalFrame 𝕜 (r + 1) N // forgetLast g = f} ≃ₜ
      Metric.sphere (0 : f.complement) 1 where
  toFun := f.lastVector
  invFun v := ⟨f.snoc v, forgetLast_snoc f v⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp [lastVector]
    · simpa only [snoc_castSucc, forgetLast_apply] using
        (congrArg (fun h : finiteOrthonormalFrame 𝕜 r N ↦ h.1 i) g.2).symm
  right_inv v := by ext; simp [lastVector]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 _).comp
      ((continuous_apply (Fin.last r)).comp
        (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := (continuous_snoc f).subtype_mk _

@[simp] theorem forgetLastFiberHomeomorph_apply (f : finiteOrthonormalFrame 𝕜 r N)
    (g : {g : finiteOrthonormalFrame 𝕜 (r + 1) N // forgetLast g = f}) :
    f.forgetLastFiberHomeomorph g = f.lastVector g := (rfl)

@[simp] theorem forgetLastFiberHomeomorph_symm_apply (f : finiteOrthonormalFrame 𝕜 r N)
    (v : Metric.sphere (0 : f.complement) 1) :
    f.forgetLastFiberHomeomorph.symm v = ⟨f.snoc v, forgetLast_snoc f v⟩ := (rfl)

/-- The fibre of the last-vector forgetful map is the unit sphere in a coordinate space
of dimension `N - r` over `𝕜`. The orthonormal coordinates on the complement are noncanonical. -/
def forgetLastFiberSphere (f : finiteOrthonormalFrame 𝕜 r N) :
    {g : finiteOrthonormalFrame 𝕜 (r + 1) N // forgetLast g = f} ≃ₜ
      Metric.sphere (0 : EuclideanSpace 𝕜 (Fin (N - r))) 1 :=
  let e := ((stdOrthonormalBasis 𝕜 f.complement).reindex
    (finCongr (finrank_complement f))).repr
  f.forgetLastFiberHomeomorph.trans (e.toHomeomorph.subtype fun x ↦ by
    simp only [mem_sphere_zero_iff_norm]
    exact (congrArg (· = 1) (e.norm_map x)).symm.to_iff)

/-- Any orthonormal frame with room for one more vector extends to an orthonormal frame. -/
theorem forgetLast_surjective (h : r < N) :
    Function.Surjective (forgetLast : finiteOrthonormalFrame 𝕜 (r + 1) N → _) := by
  intro f
  have : Nontrivial f.complement := Module.finrank_pos_iff.mp (by
    rw [finrank_complement]
    omega)
  obtain ⟨v⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := 𝕜) (E := f.complement) zero_le_one
  exact ⟨f.snoc v, forgetLast_snoc f v⟩

/-- A full frame admits no additional orthonormal vector; its forgetful fibre is empty. -/
theorem isEmpty_forgetLastFiber (h : N ≤ r) (f : finiteOrthonormalFrame 𝕜 r N) :
    IsEmpty {g : finiteOrthonormalFrame 𝕜 (r + 1) N // forgetLast g = f} := by
  have : Subsingleton f.complement :=
    (Module.finrank_eq_zero_iff_of_free 𝕜 f.complement).mp (by
      rw [finrank_complement, Nat.sub_eq_zero_of_le h])
  exact ⟨fun g ↦ isEmptyElim (f.lastVector g)⟩

/-- The forgetful map is a quotient map whenever an additional vector fits in the
ambient space. This does not by itself assert local triviality. -/
theorem isQuotientMap_forgetLast (h : r < N) :
    IsQuotientMap (forgetLast : finiteOrthonormalFrame 𝕜 (r + 1) N → _) :=
  continuous_forgetLast.isClosedMap.isQuotientMap continuous_forgetLast
    (forgetLast_surjective h)

end TauCeti.finiteOrthonormalFrame
