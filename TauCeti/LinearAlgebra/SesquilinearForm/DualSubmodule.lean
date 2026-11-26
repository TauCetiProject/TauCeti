/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# The dual submodule of a sesquilinear form

Let `K` be a commutative ring with a ring endomorphism `σ`, let `R` be a commutative coefficient
ring with `[Algebra R K]` (typically a ring of integers inside its fraction field) whose image in
`K` is mapped into itself by `σ`, and let `B : V →ₛₗ[σ] V →ₗ[K] K` be a form, `σ`-semilinear in
its first argument and linear in its second. The **dual** of an `R`-submodule
`N` of `V` is

`N^∨ = {x ∈ V | B x y ∈ R for all y ∈ N}`.

The stability of `R` under `σ` is what makes `N^∨` an `R`-submodule: `B (r • x) y = σ r * B x y`.
For `σ = id` this is Mathlib's `LinearMap.BilinForm.dualSubmodule`
(`LinearMap.dualSubmodule_eq_bilinFormDualSubmodule`); for the conjugation of a quadratic
extension `E/F` and `R = 𝓞 E` it is the dual of a hermitian or skew-hermitian lattice.

Duals are compatible with adjoint maps: if `B' w (f v) = B (g w) v`, the dual of the image `f N` is
the preimage of `N^∨` under `g` (`LinearMap.dualSubmodule_map`). The main application is the
**duality of projection and intersection**: for a subspace `Z` with a complement `Q` orthogonal
to `Z`, for instance `Q = Z^⊥` when `V = Z ⊕ Z^⊥`, and the projection `P` onto `Z` along `Q`, the
dual of `P N` taken inside `Z` for the restricted form is `N^∨ ∩ Z`
(`LinearMap.dualSubmodule_map_projectionOnto`). Only the identity `B z (P y) = B z y` for
`z ∈ Z` enters (`LinearMap.apply_projection_of_le_orthogonalBilin`): `N` is an arbitrary
`R`-submodule, and neither a symmetry of `B`, nor its nondegeneracy, nor any finiteness is
assumed. Its case of the real inner product and `R = ℤ` is
`ZLattice.dual_map_orthogonalProjectionOnto`.

For an `ε`-hermitian form, `B y x = ε σ (B x y)` with `ε = ±1`, membership in the dual may be
tested with `x` in either argument (`LinearMap.mem_dualSubmodule_iff_flip`).

## Main definitions

* `LinearMap.dualSubmodule B hσ N`: the dual `{x | ∀ y ∈ N, B x y ∈ R}` of an `R`-submodule `N`.

## Main statements

* `LinearMap.dualSubmodule_anti`, `LinearMap.dualSubmodule_sup`: dualizing reverses inclusions
  and takes sums to intersections.
* `LinearMap.dualSubmodule_map`: the dual of an image under a map with an adjoint is the preimage
  of the dual under the adjoint.
* `LinearMap.apply_projection_of_le_orthogonalBilin`: `B z (P v) = B z v` for `z ∈ Z` and the
  projection `P` onto `Z` along a complement orthogonal to `Z`.
* `LinearMap.dualSubmodule_map_projectionOnto`: the dual of the projection of `N` to `Z` along a
  complement orthogonal to `Z` is `N^∨ ∩ Z`.

## Provenance

`LinearMap.dualSubmodule_map_projectionOnto` is adapted from `New.Grading.formFin_stringProj` and
`New.Grading.mem_latticeMinus_iff_formFin` (file `src/Lib/Weil/Periods/PointLattice.lean`) in
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which
prove it for a self-dual lattice over the finite adeles of a CM field and a coordinate projection
along the string of a grading, testing membership with the lattice vector in the first argument.
The dual submodule of a sesquilinear form, the statement for an arbitrary submodule, coefficient
ring and complement, and the general adjoint form `LinearMap.dualSubmodule_map` are new here.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §82, for dual lattices.
* T. Horesh and Y. Karasik, *Equidistribution of primitive lattices in `ℝⁿ`*, Quart. J. Math. 74
  (2023), 1253–1294, Proposition B.5, for the duality of projection and intersection for lattices
  in a euclidean space.
-/

public section

namespace LinearMap

section Semiring

variable {R K V W : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]
  [AddCommMonoid V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommMonoid W] [Module K W] [Module R W] [IsScalarTower R K W] {σ : K →+* K}
  (B : V →ₛₗ[σ] V →ₗ[K] K) (hσ : ∀ r : R, σ (algebraMap R K r) ∈ (1 : Submodule R K))

/-- The **dual submodule** of an `R`-submodule `N` for a form `B`, `σ`-semilinear in its first
argument: the vectors `x` with `B x y ∈ R` for every `y ∈ N`. The hypothesis `hσ`, that `σ` maps
the image of `R` into itself, makes it an `R`-submodule. -/
def dualSubmodule (N : Submodule R V) : Submodule R V where
  carrier := {x | ∀ y ∈ N, B x y ∈ (1 : Submodule R K)}
  add_mem' {a b} ha hb y hy := by
    rw [map_add, LinearMap.add_apply]
    exact add_mem (ha y hy) (hb y hy)
  zero_mem' y _ := by
    rw [map_zero, LinearMap.zero_apply]
    exact zero_mem _
  smul_mem' r x hx y hy := by
    rw [← algebraMap_smul K r x, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hσ r)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx y hy)
    exact Submodule.mem_one.2 ⟨a * b, by rw [map_mul, ha, hb]⟩

variable {B hσ} in
/-- A vector lies in the dual of `N` if and only if its products with the vectors of `N` lie in
`R`. -/
theorem mem_dualSubmodule {N : Submodule R V} {x : V} :
    x ∈ B.dualSubmodule hσ N ↔ ∀ y ∈ N, B x y ∈ (1 : Submodule R K) :=
  Iff.rfl

/-- Dualizing reverses inclusions. -/
theorem dualSubmodule_anti : Antitone (B.dualSubmodule hσ) :=
  fun _ _ h _ hx y hy ↦ hx y (h hy)

/-- Every vector lies in the dual of the zero submodule. -/
@[simp]
theorem dualSubmodule_bot : B.dualSubmodule hσ ⊥ = ⊤ :=
  eq_top_iff.2 fun x _ y hy ↦ by
    rw [(Submodule.mem_bot R).1 hy, map_zero]
    exact zero_mem _

/-- The dual of a sum of submodules is the intersection of their duals. -/
@[simp]
theorem dualSubmodule_sup (N₁ N₂ : Submodule R V) :
    B.dualSubmodule hσ (N₁ ⊔ N₂) = B.dualSubmodule hσ N₁ ⊓ B.dualSubmodule hσ N₂ := by
  refine le_antisymm (le_inf (B.dualSubmodule_anti hσ le_sup_left)
    (B.dualSubmodule_anti hσ le_sup_right)) fun x hx y hy ↦ ?_
  obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.1 hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add]
  exact add_mem (mem_dualSubmodule.1 hx₁ y₁ hy₁) (mem_dualSubmodule.1 hx₂ y₂ hy₂)

/-- **Duals of images.** Let `B` and `B'` be forms on `V` and `W`, and `f : V → W`, `g : W → V`
`R`-linear maps adjoint to each other, `B' w (f v) = B (g w) v`. The dual of the image `f N` is
the preimage of the dual `N^∨` under `g`. -/
theorem dualSubmodule_map (B' : W →ₛₗ[σ] W →ₗ[K] K) {f : V →ₗ[R] W} {g : W →ₗ[R] V}
    (hfg : ∀ w v, B' w (f v) = B (g w) v) (N : Submodule R V) :
    B'.dualSubmodule hσ (N.map f) = (B.dualSubmodule hσ N).comap g := by
  ext w
  simp only [mem_dualSubmodule, Submodule.mem_comap, Submodule.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, hfg]

end Semiring

section Ring

variable {R K V : Type*} [CommSemiring R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] {σ : K →+* K}
  (B : V →ₛₗ[σ] V →ₗ[K] K) (hσ : ∀ r : R, σ (algebraMap R K r) ∈ (1 : Submodule R K))

/-- For a vector `z` of `Z` and a complement `Q` of `Z` orthogonal to `Z`, the form does not see
the difference between a vector and its projection to `Z` along `Q`: `B z (P v) = B z v`. -/
theorem apply_projection_of_le_orthogonalBilin {Z Q : Submodule K V} (h : IsCompl Z Q)
    (hQ : Q ≤ Z.orthogonalBilin B) {z : V} (hz : z ∈ Z) (v : V) :
    B z (Z.projection Q h v) = B z v := by
  have := Submodule.mem_orthogonalBilin.1 (hQ (Submodule.sub_projection_mem h v)) z hz
  rwa [map_sub, sub_eq_zero, eq_comm] at this

/-- **Duality of projection and intersection.** Let `Z` be a subspace of `V` with a complement
`Q` orthogonal to it (`B z q = 0` for `z ∈ Z`, `q ∈ Q`), for instance `Q = Z^⊥` when
`V = Z ⊕ Z^⊥`, and let `P` be the projection onto `Z` along `Q`. For every `R`-submodule `N`,
the dual of `P N` taken inside `Z` for the restricted form is `N^∨ ∩ Z`. -/
theorem dualSubmodule_map_projectionOnto {Z Q : Submodule K V} (h : IsCompl Z Q)
    (hQ : Q ≤ Z.orthogonalBilin B) (N : Submodule R V) :
    (B.domRestrict₁₂ Z Z).dualSubmodule hσ (N.map ((Z.projectionOnto Q h).restrictScalars R)) =
      (B.dualSubmodule hσ N).comap (Z.subtype.restrictScalars R) :=
  dualSubmodule_map B hσ _ (fun z v ↦ by
    simp [domRestrict₁₂_apply, apply_projection_of_le_orthogonalBilin B h hQ z.property]) N

/-- **Duality of projection and intersection** for the orthogonal decomposition
`V = Z ⊕ Z^⊥`: for the projection `P` onto `Z` along `Z^⊥` and every `R`-submodule `N`, the dual
of `P N` taken inside `Z` is `N^∨ ∩ Z`. -/
theorem dualSubmodule_map_projectionOnto_orthogonalBilin {Z : Submodule K V}
    (h : IsCompl Z (Z.orthogonalBilin B)) (N : Submodule R V) :
    (B.domRestrict₁₂ Z Z).dualSubmodule hσ (N.map ((Z.projectionOnto _ h).restrictScalars R)) =
      (B.dualSubmodule hσ N).comap (Z.subtype.restrictScalars R) :=
  dualSubmodule_map_projectionOnto B hσ h le_rfl N

end Ring

section SignedHermitian

variable {R K V : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] {σ : K →+* K}
  {B : V →ₛₗ[σ] V →ₗ[K] K} {hσ : ∀ r : R, σ (algebraMap R K r) ∈ (1 : Submodule R K)}

/-- For an `ε`-hermitian form, `B w v = ε σ (B v w)` with `ε = ±1`, membership in the dual can
be tested with the vector in the second argument: `x ∈ N^∨` if and only if `B y x ∈ R` for every
`y ∈ N`. -/
theorem mem_dualSubmodule_iff_flip {ε : ℤˣ} (hB : ∀ v w, B w v = ε • σ (B v w))
    {N : Submodule R V} {x : V} :
    x ∈ B.dualSubmodule hσ N ↔ ∀ y ∈ N, B y x ∈ (1 : Submodule R K) := by
  have key (c : K) (hc : c ∈ (1 : Submodule R K)) : ε • σ c ∈ (1 : Submodule R K) := by
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hc
    rw [Units.smul_def]
    exact Submodule.smul_of_tower_mem _ _ (hσ a)
  refine ⟨fun hx y hy ↦ ?_, fun hx y hy ↦ ?_⟩
  · rw [hB x y]
    exact key _ (hx y hy)
  · rw [hB y x]
    exact key _ (hx y hy)

end SignedHermitian

section BilinForm

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- For `σ = id` the dual submodule is Mathlib's `LinearMap.BilinForm.dualSubmodule`. -/
theorem dualSubmodule_eq_bilinFormDualSubmodule (B : LinearMap.BilinForm K V)
    (hσ : ∀ r : R, RingHom.id K (algebraMap R K r) ∈ (1 : Submodule R K)) (N : Submodule R V) :
    LinearMap.dualSubmodule B hσ N = B.dualSubmodule N :=
  Submodule.ext fun _ ↦ mem_dualSubmodule.trans (BilinForm.mem_dualSubmodule B).symm

end BilinForm

end LinearMap
