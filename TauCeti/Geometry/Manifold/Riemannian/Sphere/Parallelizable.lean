/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.TangentBundle
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.InnerProduct

/-!
# Clifford orthonormal tangent frames and parallelizability of `S⁰`, `S¹`, `S³`, `S⁷`

Let `E` be an `(n + 1)`-dimensional real inner product space. Any skew-adjoint action
`ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E` produces `m` analytic (`C^ω`, and
hence `C^k` for every `k : ℕ∞ω`) pointwise orthonormal tangent vector fields on the unit sphere
`sphere (0 : E) 1` (`TauCeti.cliffordSphereFrame`). At each `x : sphere (0 : E) 1`, the `i`-th
field is the lift along `TauCeti.sphereTangentEquiv x` of `ρ (ι _ (Pi.single i 1)) x ∈ (ℝ ∙ x)ᗮ`.

When `m = n`, these `n` fields form a global `C^k` orthonormal tangent frame and induce an explicit
`C^k` tangent-bundle trivialization
`TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^k sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` by
inner-product coordinates (`TauCeti.cliffordSphereTangentDiffeomorph`).

Combining this construction with `TauCeti.exists_isSkewAdjoint_inner_realCliffordForm_zero` (built
from the real Clifford classification `Cliff(0, 0) ≅ ℝ`, `Cliff(0, 1) ≅ ℂ`,
`Cliff(0, 3) ≅ ℍ × ℍ`, and `Cliff(0, 7) ≅ M₈(ℝ) × M₈(ℝ)`) proves that `S⁰`, `S¹`, `S³`, and `S⁷`
admit analytic orthonormal global tangent frames and global tangent-bundle trivializations:

* `TauCeti.sphereZeroTangentDiffeomorph`: explicit global trivialization of `TS⁰` via the empty
  frame.
* `TauCeti.exists_orthonormal_contMDiff_sphere_of_mem` and
  `TauCeti.nonempty_sphereTangent_diffeomorph_of_mem`: smooth (`C^k` for all `k : ℕ∞ω`) orthonormal
  global frames and tangent-bundle trivializations on `sphere (0 : E) 1` for
  `n ∈ {0, 1, 3, 7}`.
* `TauCeti.exists_contMDiff_linearIndependent_sphere_euclideanSpace`: specialization to the
  standard sphere `sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` at every regularity `k : ℕ∞ω`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter I, §7 (vector fields on spheres from Clifford modules).
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1, p. 5.
* J. F. Adams, *Vector fields on spheres*, Annals of Mathematics 75 (1962), 603--632.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Metric Module
open scoped ContDiff Manifold

namespace TauCeti

section CliffordFrame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n m : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The `m` tangent vector fields on `sphere (0 : E) 1` induced by a skew-adjoint action of
`CliffordAlgebra (realCliffordForm 0 m)` on `E`: at `x`, the `i`-th field has ambient value
`ρ (ι (realCliffordForm 0 m) (Pi.single (Fin.natAdd 0 i) 1)) x`. -/
def cliffordSphereFrame (ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 m) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 m) v) y))
    (i : Fin m) (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv x).symm
    ⟨ρ (ι (realCliffordForm 0 m) (Pi.single (Fin.natAdd 0 i) 1)) (x : E),
      ρ.map_cliffordAlgebraι_mem_orthogonal_span_singleton (hskew _) (x : E)⟩

@[simp]
theorem sphereTangentEquiv_cliffordSphereFrame
    (ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 m) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 m) v) y))
    (i : Fin m) (x : sphere (0 : E) 1) :
    sphereTangentEquiv x (cliffordSphereFrame (n := n) ρ hskew i x) =
      ⟨ρ (ι (realCliffordForm 0 m) (Pi.single (Fin.natAdd 0 i) 1)) (x : E),
        ρ.map_cliffordAlgebraι_mem_orthogonal_span_singleton (hskew _) (x : E)⟩ :=
  LinearIsometryEquiv.apply_symm_apply _ _

theorem coe_sphereTangentEquiv_cliffordSphereFrame
    (ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 m) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 m) v) y))
    (i : Fin m) (x : sphere (0 : E) 1) :
    (sphereTangentEquiv x (cliffordSphereFrame (n := n) ρ hskew i x) : E) =
      ρ (ι (realCliffordForm 0 m) (Pi.single (Fin.natAdd 0 i) 1)) (x : E) := by
  rw [sphereTangentEquiv_cliffordSphereFrame]

@[simp]
theorem mfderiv_subtypeVal_cliffordSphereFrame
    (ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 m) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 m) v) y))
    (i : Fin m) (x : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x
        (cliffordSphereFrame (n := n) ρ hskew i x) =
      ρ (ι (realCliffordForm 0 m) (Pi.single (Fin.natAdd 0 i) 1)) (x : E) := by
  rw [← coe_sphereTangentEquiv_apply, coe_sphereTangentEquiv_cliffordSphereFrame]

/-- Each Clifford vector field on `sphere (0 : E) 1` is `C^k` at every regularity `k : ℕ∞ω`
(in particular analytic, `k = ω`, and smooth, `k = ∞`). -/
theorem contMDiff_cliffordSphereFrame {k : ℕ∞ω}
    (ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 m) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 m) v) y))
    (i : Fin m) :
    ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, cliffordSphereFrame (n := n) ρ hskew i x⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  refine (contMDiff_sphereTangentEquiv_symm_iff _).mpr ?_
  let L : E →L[ℝ] E :=
    LinearMap.toContinuousLinearMap (ρ (ι (realCliffordForm 0 m) (Pi.single (Fin.natAdd 0 i) 1)))
  exact L.contDiff.contMDiff.comp contMDiff_coe_sphere

/-- At every point `x` of the unit sphere, the Clifford tangent vectors
`cliffordSphereFrame ρ hskew · x` are orthonormal for the round metric. -/
theorem orthonormal_cliffordSphereFrame
    (ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 m) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 m) v) y))
    (x : sphere (0 : E) 1) :
    Orthonormal ℝ fun i ↦ cliffordSphereFrame (n := n) ρ hskew i x := by
  have horth : ∀ i j : Fin m, i ≠ j →
      (realCliffordForm 0 m).IsOrtho (Pi.single (Fin.natAdd 0 i) 1)
        (Pi.single (Fin.natAdd 0 j) 1) :=
    fun i j hij ↦ isOrtho_realCliffordForm_single (fun h ↦ hij (Fin.natAdd_injective m 0 h)) 1 1
  have hQ (i : Fin m) : realCliffordForm 0 m (Pi.single (Fin.natAdd 0 i) 1) = -1 :=
    realCliffordForm_single_one_of_le (Nat.zero_le _)
  have hon := ρ.orthonormal_orthogonal_map_cliffordAlgebraι_apply horth hQ
    (fun i ↦ hskew _) (norm_eq_of_mem_sphere x)
  exact (sphereTangentEquiv x).symm.toLinearIsometry.orthonormal_comp_iff.mpr hon

/-- Pointwise linear independence of the Clifford tangent vector fields on `sphere (0 : E) 1`. -/
theorem linearIndependent_cliffordSphereFrame
    (ρ : CliffordAlgebra (realCliffordForm 0 m) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 m) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 m) v) y))
    (x : sphere (0 : E) 1) :
    LinearIndependent ℝ fun i ↦ cliffordSphereFrame (n := n) ρ hskew i x :=
  (orthonormal_cliffordSphereFrame ρ hskew x).linearIndependent

/-- A skew-adjoint `CliffordAlgebra (realCliffordForm 0 n)`-action on an `(n + 1)`-dimensional real
inner product space `E` trivializes `TangentBundle (𝓡 n) (sphere (0 : E) 1)` globally at every
regularity `k : ℕ∞ω` via inner-product coordinates against `TauCeti.cliffordSphereFrame`. -/
def cliffordSphereTangentDiffeomorph {k : ℕ∞ω}
    (ρ : CliffordAlgebra (realCliffordForm 0 n) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 n) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 n) v) y)) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^k⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      (sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) :=
  sphereTangentDiffeomorphOfOrthonormal (orthonormal_cliffordSphereFrame ρ hskew)
    (contMDiff_cliffordSphereFrame ρ hskew)

@[simp]
theorem cliffordSphereTangentDiffeomorph_apply_fst {k : ℕ∞ω}
    (ρ : CliffordAlgebra (realCliffordForm 0 n) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 n) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 n) v) y))
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    (cliffordSphereTangentDiffeomorph (k := k) ρ hskew p).1 = p.proj := by
  rw [cliffordSphereTangentDiffeomorph, sphereTangentDiffeomorphOfOrthonormal_apply_fst]

@[simp]
theorem cliffordSphereTangentDiffeomorph_apply_snd {k : ℕ∞ω}
    (ρ : CliffordAlgebra (realCliffordForm 0 n) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 n) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 n) v) y))
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) (i : Fin n) :
    ((cliffordSphereTangentDiffeomorph (k := k) ρ hskew p).2).ofLp i =
      inner ℝ (ρ (ι (realCliffordForm 0 n) (Pi.single (Fin.natAdd 0 i) 1)) (p.proj : E))
        (sphereTangentEquiv p.proj p.2 : E) := by
  rw [cliffordSphereTangentDiffeomorph, sphereTangentDiffeomorphOfOrthonormal_apply_snd,
    inner_tangentSpace_sphere, mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv,
    mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv, coe_sphereTangentEquiv_cliffordSphereFrame]

@[simp]
theorem cliffordSphereTangentDiffeomorph_symm_apply {k : ℕ∞ω}
    (ρ : CliffordAlgebra (realCliffordForm 0 n) →ₐ[ℝ] Module.End ℝ E)
    (hskew : ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 n) v) x) y =
      -inner ℝ x (ρ (ι (realCliffordForm 0 n) v) y))
    (q : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) :
    (cliffordSphereTangentDiffeomorph (k := k) ρ hskew).symm q =
      ⟨q.1, ∑ i, q.2.ofLp i • cliffordSphereFrame ρ hskew i q.1⟩ := by
  rw [cliffordSphereTangentDiffeomorph, sphereTangentDiffeomorphOfOrthonormal_symm_apply]

end CliffordFrame

/-! ### Explicit rank-zero trivialization of `TS⁰` -/

section SphereZero

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 0 + 1)]

/-- Explicit global `C^k` trivialization of the rank-zero tangent bundle of `S⁰` induced by the
empty orthonormal frame. -/
def sphereZeroTangentDiffeomorph {k : ℕ∞ω} :
    TangentBundle (𝓡 0) (sphere (0 : E) 1) ≃ₘ^k⟮(𝓡 0).tangent,
      (𝓡 0).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))⟯
      (sphere (0 : E) 1 × EuclideanSpace ℝ (Fin 0)) :=
  sphereTangentDiffeomorphOfOrthonormal
    (v := fun (i : Fin 0) _ ↦ i.elim0) (fun _ ↦ .of_isEmpty _) fun i ↦ i.elim0

@[simp]
theorem sphereZeroTangentDiffeomorph_apply_fst {k : ℕ∞ω}
    (p : TangentBundle (𝓡 0) (sphere (0 : E) 1)) :
    (sphereZeroTangentDiffeomorph (k := k) p).1 = p.proj := by
  rw [sphereZeroTangentDiffeomorph, sphereTangentDiffeomorphOfOrthonormal_apply_fst]

@[simp]
theorem sphereZeroTangentDiffeomorph_symm_apply {k : ℕ∞ω}
    (q : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin 0)) :
    (sphereZeroTangentDiffeomorph (k := k)).symm q = ⟨q.1, 0⟩ := by
  rw [sphereZeroTangentDiffeomorph, sphereTangentDiffeomorphOfOrthonormal_symm_apply,
    Finset.univ_eq_empty, Finset.sum_empty]

end SphereZero

/-! ### Parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷` -/

section HurwitzSpheres

/-- **Smooth orthonormal frames on `S⁰`, `S¹`, `S³`, and `S⁷`.** For `n ∈ {0, 1, 3, 7}` and any
`(n + 1)`-dimensional real inner product space `E`, the unit sphere `sphere (0 : E) 1` admits `n`
pointwise orthonormal `C^k` tangent vector fields for every `k : ℕ∞ω` (including `k = ω` and
`k = ∞`). -/
theorem exists_orthonormal_contMDiff_sphere_of_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (k : ℕ∞ω) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
        (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) ∧
      ∀ x, Orthonormal ℝ fun i ↦ v i x := by
  obtain ⟨ρ, hskew⟩ := exists_isSkewAdjoint_inner_realCliffordForm_zero (E := E) Fact.out hn
  exact ⟨cliffordSphereFrame ρ hskew, contMDiff_cliffordSphereFrame ρ hskew,
    orthonormal_cliffordSphereFrame ρ hskew⟩

/-- **Global tangent-bundle trivialization for `S⁰`, `S¹`, `S³`, and `S⁷`.** For
`n ∈ {0, 1, 3, 7}` and any `(n + 1)`-dimensional real inner product space `E`,
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` is `C^k`-diffeomorphic to
`sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` for every `k : ℕ∞ω`. -/
theorem nonempty_sphereTangent_diffeomorph_of_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (k : ℕ∞ω) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^k⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      (sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨ρ, hskew⟩ := exists_isSkewAdjoint_inner_realCliffordForm_zero (E := E) Fact.out hn
  exact ⟨cliffordSphereTangentDiffeomorph ρ hskew⟩

/-- **Parallelizability of standard `S⁰`, `S¹`, `S³`, and `S⁷`.** For `n ∈ {0, 1, 3, 7}` and every
regularity `k : ℕ∞ω`, the standard unit sphere in `EuclideanSpace ℝ (Fin (n + 1))` admits `n`
`C^k` tangent vector fields that are linearly independent at every point. -/
theorem exists_contMDiff_linearIndependent_sphere_euclideanSpace
    {n : ℕ} (k : ℕ∞ω) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    letI := finrank_euclideanSpace_fin_succ_fact n
    ∃ v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) k
        (fun x ↦ (⟨x, v i x⟩ :
          TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))) ∧
      ∀ x, LinearIndependent ℝ fun i ↦ v i x := by
  let := finrank_euclideanSpace_fin_succ_fact n
  obtain ⟨v, hv, horth⟩ := exists_orthonormal_contMDiff_sphere_of_mem
    (E := EuclideanSpace ℝ (Fin (n + 1))) k hn
  exact ⟨v, hv, fun x ↦ (horth x).linearIndependent⟩

end HurwitzSpheres

end TauCeti
