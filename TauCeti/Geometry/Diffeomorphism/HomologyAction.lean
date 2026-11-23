/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.HomeomorphAction
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Diffeomorphism.Evaluation
public import TauCeti.Geometry.Manifold.Diffeomorph.Prod
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The action of diffeomorphisms on singular homology

A `C^n` diffeomorphism of a manifold `M` acts on each singular homology group `Hₘ(M; R)` through
its underlying homeomorphism (`Homeomorph.singularHomologyAction` composed with
`Diffeomorph.toHomeomorphHom`). On a compact manifold with locally compact model, evaluation is
continuous for the weak Whitney topology on `Diff(M)`, so a path from the identity to `φ` in
`Diff(M)` is a homotopy from the identity of `M` to `φ`. Hence every diffeomorphism in the identity
path component of `Diff(M)` acts trivially on homology
(`Diffeomorph.singularHomologyAction_toHomeomorphHom_eq_one_of_joined`): the action factors through
the group of isotopy classes. Consequently a diffeomorphism acting nontrivially on homology is not
isotopic to the identity. For the factor swap `(x, y) ↦ (y, x)` of `M × M` this holds as soon as
`M` is nonempty and has nontrivial homology in some positive degree
(`Diffeomorph.not_joined_one_prodComm`).

For a smooth form `σ` on `M`, such as a symplectic form, the diffeomorphisms preserving `σ` form
the stabilizer `TauCeti.SmoothForm.diffeomorphStabilizer σ`, the symplectomorphism group when `σ`
is symplectic. Its **homologically trivial** part
`TauCeti.SmoothForm.homologicallyTrivialStabilizer σ R m` is the kernel of its action on
`Hₘ(M; R)`. For the product of two area forms of equal area on `S² × S²`, with `m = 2` and integral
coefficients, this is the group `G₀` in Gromov's description of the symplectomorphism group of
`S² × S²`: the full group acts on `H₂(S² × S²; ℤ) = ℤ A ⊕ ℤ B` by permuting the classes `A` and `B`
of the two rulings. The kernel is a normal subgroup of the stabilizer and contains the identity
path component of the stabilizer
(`TauCeti.SmoothForm.coe_mem_homologicallyTrivialStabilizer_of_joined`). The factor swap is never
in it: for a compact connected oriented manifold `M` of positive dimension `n`, the swap of
`M × M` exchanges the images of the fundamental class `[M]` under the inclusions of the two factors,
which differ in `Hₙ(M × M; ℤ)`
(`TauCeti.HomologicalOrientation.prodComm_notMem_homologicallyTrivialStabilizer`). The case
`S² × S²` is in `TauCeti.Geometry.Diffeomorphism.Sphere.HomologyAction`.

## Main definitions

* `TauCeti.SmoothForm.homologicallyTrivialStabilizer σ R m`: the diffeomorphisms preserving `σ`
  and acting trivially on `Hₘ(M; R)`.

## Main results

* `Diffeomorph.singularHomologyAction_toHomeomorphHom_eq_one_of_joined`: diffeomorphisms joined
  to the identity in `Diff(M)` act trivially on singular homology.
* `Diffeomorph.singularHomologyAction_toHomeomorphHom_prodComm_ne_one`,
  `Diffeomorph.not_joined_one_prodComm`: the factor swap of `M × M` acts nontrivially on
  homology, so it is not joined to the identity.
* `TauCeti.SmoothForm.coe_mem_homologicallyTrivialStabilizer_of_joined`: the identity path
  component of the stabilizer of `σ` acts trivially on homology.
* `TauCeti.SmoothForm.prodComm_notMem_homologicallyTrivialStabilizer`,
  `TauCeti.HomologicalOrientation.prodComm_notMem_homologicallyTrivialStabilizer`: the factor swap
  acts nontrivially on homology.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §2.4 (the symplectomorphism group of `S² × S²`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52** (2012), §9.5.
-/

public section

open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

universe u

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {k : Type u} [Ring k] {R : ModuleCat.{u} k} {m : ℕ}

/-- **The factor swap acts nontrivially on homology.** If `M` is nonempty and has nontrivial
singular homology `Hₘ(M; R)` in a positive degree `m`, the factor swap of `M × M` acts
nontrivially on `Hₘ(M × M; R)`. -/
theorem singularHomologyAction_toHomeomorphHom_prodComm_ne_one [Nonempty M] (hm : m ≠ 0)
    [Nontrivial (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) m).obj R).obj
      (TopCat.of M))] :
    Homeomorph.singularHomologyAction R m (toHomeomorphHom (Diffeomorph.prodComm I I M M n)) ≠
      1 := by
  rw [toHomeomorphHom_apply, toHomeomorph_prodComm]
  exact Homeomorph.singularHomologyAction_prodComm_ne_one R m hm

variable [LocallyCompactSpace E] [CompactSpace M] [IsManifold I n M]

/-- **Diffeomorphisms isotopic to the identity act trivially on singular homology.** On a compact
manifold, a diffeomorphism joined to the identity by a path in `Diff(M)` (for the weak Whitney
topology) is homotopic to the identity through evaluation along the path, so it induces the
identity on `Hₘ(M; R)`. -/
theorem singularHomologyAction_toHomeomorphHom_eq_one_of_joined {φ : M ≃ₘ^n⟮I, I⟯ M}
    (h : Joined 1 φ) : Homeomorph.singularHomologyAction R m (toHomeomorphHom φ) = 1 := by
  refine Homeomorph.singularHomologyAction_eq_one_of_homotopic ⟨?_⟩
  let γ := h.somePath
  exact
    { toFun := fun p ↦ γ p.fst p.snd
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by simp [γ, one_def]
      map_one_left := fun x ↦ by simp [γ, toHomeomorphHom_apply] }

/-- **The factor swap is not isotopic to the identity.** If the compact manifold `M` is nonempty
and has nontrivial singular homology `Hₘ(M; R)` in a positive degree `m`, the swap
`(x, y) ↦ (y, x)` of `M × M` is not joined to the identity in `Diff(M × M)`, since it acts
nontrivially on `Hₘ(M × M; R)`. -/
theorem not_joined_one_prodComm [Nonempty M] (hm : m ≠ 0)
    [Nontrivial (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) m).obj R).obj
      (TopCat.of M))] :
    ¬ Joined 1 (Diffeomorph.prodComm I I M M n) := fun h ↦
  singularHomologyAction_toHomeomorphHom_prodComm_ne_one (R := R) hm
    (singularHomologyAction_toHomeomorphHom_eq_one_of_joined h)

end Diffeomorph

namespace TauCeti.SmoothForm

open Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}
  {k : Type u} [Ring k] {R : ModuleCat.{u} k} {m : ℕ}

variable (σ : SmoothForm I M F j) (R m) in
/-- The **homologically trivial stabilizer** of a smooth form `σ`: the diffeomorphisms preserving
`σ` that act trivially on `Hₘ(M; R)`, the kernel of the action of the stabilizer
`diffeomorphStabilizer σ` on `Hₘ(M; R)`. For a symplectic form `ω` on a four-manifold, `m = 2`
and `R = ℤ`, this is the group `G₀` of symplectomorphisms acting trivially on `H₂(M; ℤ)`. -/
noncomputable def homologicallyTrivialStabilizer : Subgroup (M ≃ₘ⟮I, I⟯ M) :=
  diffeomorphStabilizer σ ⊓
    ((Homeomorph.singularHomologyAction R m).comp (toHomeomorphHom (n := ∞))).ker

variable {σ : SmoothForm I M F j}

/-- A diffeomorphism lies in the homologically trivial stabilizer of `σ` exactly when it preserves
`σ` and acts trivially on `Hₘ(M; R)`. -/
@[simp]
theorem mem_homologicallyTrivialStabilizer {φ : M ≃ₘ⟮I, I⟯ M} :
    φ ∈ σ.homologicallyTrivialStabilizer R m ↔
      φ ∈ diffeomorphStabilizer σ ∧
        Homeomorph.singularHomologyAction R m (toHomeomorphHom φ) = 1 :=
  Iff.rfl

/-- The homologically trivial stabilizer of `σ` is contained in the stabilizer of `σ`. -/
theorem homologicallyTrivialStabilizer_le_diffeomorphStabilizer :
    σ.homologicallyTrivialStabilizer R m ≤ diffeomorphStabilizer σ :=
  inf_le_left

/-- The homologically trivial stabilizer is a normal subgroup of the stabilizer, being the kernel
of its action on `Hₘ(M; R)`. -/
instance normal_homologicallyTrivialStabilizer_subgroupOf :
    ((σ.homologicallyTrivialStabilizer R m).subgroupOf (diffeomorphStabilizer σ)).Normal := by
  rw [homologicallyTrivialStabilizer, Subgroup.inf_subgroupOf_left]
  exact Subgroup.normal_subgroupOf

/-- **The factor swap acts nontrivially on homology.** If the manifold `M` is nonempty and has
nontrivial homology `Hₘ(M; R)` in a positive degree `m`, then for every smooth form `σ` on
`M × M`, the swap `(x, y) ↦ (y, x)` does not lie in the homologically trivial stabilizer of `σ`,
whether or not it preserves `σ`. -/
theorem prodComm_notMem_homologicallyTrivialStabilizer [Nonempty M] (hm : m ≠ 0)
    [Nontrivial (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) m).obj R).obj
      (TopCat.of M))] (σ : SmoothForm (I.prod I) (M × M) F j) :
    Diffeomorph.prodComm I I M M ∞ ∉ σ.homologicallyTrivialStabilizer R m := fun h ↦
  singularHomologyAction_toHomeomorphHom_prodComm_ne_one hm
    (mem_homologicallyTrivialStabilizer.mp h).right

variable [LocallyCompactSpace E] [CompactSpace M]

/-- **The identity path component of the stabilizer acts trivially on homology.** On a compact
manifold, a diffeomorphism joined to the identity by a path of diffeomorphisms preserving `σ`, for
the weak Whitney topology, lies in the homologically trivial stabilizer of `σ`. -/
theorem coe_mem_homologicallyTrivialStabilizer_of_joined {φ : diffeomorphStabilizer σ}
    (h : Joined 1 φ) : (φ : M ≃ₘ⟮I, I⟯ M) ∈ σ.homologicallyTrivialStabilizer R m :=
  ⟨φ.property, singularHomologyAction_toHomeomorphHom_eq_one_of_joined
    (h.map (f := ((↑) : diffeomorphStabilizer σ → M ≃ₘ⟮I, I⟯ M)) continuous_subtypeVal)⟩

end TauCeti.SmoothForm

namespace TauCeti.HomologicalOrientation

open SmoothForm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [ConnectedSpace M] {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {j : ℕ}

/-- **The factor swap of the square of a closed oriented manifold acts nontrivially on
`Hₙ(M × M; ℤ)`, `n = dim M`.** For a compact connected oriented manifold `M` of positive
dimension `n` and every smooth form `σ` on `M × M`, the swap `(x, y) ↦ (y, x)` does not lie in the
homologically trivial stabilizer of `σ` for `Hₙ(M × M; ℤ)`: it exchanges the images of the
fundamental class `[M]` under the inclusions of the two factors. -/
theorem prodComm_notMem_homologicallyTrivialStabilizer (o : HomologicalOrientation M E n)
    (hn : Module.finrank ℝ E = n) (hn0 : n ≠ 0)
    (σ : SmoothForm (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (M × M) F j) :
    Diffeomorph.prodComm 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞ ∉
      σ.homologicallyTrivialStabilizer (ModuleCat.of ℤ (ULift.{0} ℤ)) n :=
  have : Nonempty M := ConnectedSpace.toNonempty
  have : Nontrivial (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M)) := o.nontrivial_singularHomology hn
  SmoothForm.prodComm_notMem_homologicallyTrivialStabilizer hn0 σ

end TauCeti.HomologicalOrientation
