/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Geometry.Diffeomorphism.Inversion
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization

/-!
# Evaluation on the diffeomorphism group of a compact Lie group

Let `G` be a compact `C^n` Lie group, and give its group `Diff(G)` of `C^n` self-diffeomorphisms
the weak Whitney topology. A `C^n` action of a Lie group on a compact manifold `M` is a continuous
homomorphism into `Diff(M)` (`Diffeomorph.smulContinuousMonoidHom`), since a jointly `C^n` family
of diffeomorphisms is continuous for the weak Whitney topology. In particular the left translations
`L_a : x ↦ a * x` of `G` form a continuous homomorphism `G →ₜ* Diff(G)`.

For a point `x₀ : G`, the left translations by `z * x₀⁻¹` form a continuous section
`z ↦ L_{z x₀⁻¹}` of evaluation `Diff(G) → G`, `g ↦ g x₀`, defined on all of `G`
(`TauCeti.Lie.leftTranslationSection`). So evaluation at `x₀` is a *trivial* principal bundle
with fibre the stabilizer `Diff(G, x₀)` of `x₀`: the map `g ↦ (g x₀, L_{g(x₀) x₀⁻¹}⁻¹ ∘ g)` is a
homeomorphism

`Diff(G) ≃ₜ G × Diff(G, x₀)`

with inverse `(z, h) ↦ L_{z x₀⁻¹} ∘ h` (`TauCeti.Lie.diffeomorphHomeomorphProdStabilizer`). For a
general compact manifold, evaluation is only locally trivial over the orbit of `x₀`, with local
sections built from cut-off translations in charts
(`TauCeti.exists_trivialization_diffeomorph_apply`); on a Lie group the translations of the group
itself give one section over all of `G`. For the circle `S¹ ⊆ ℂ` the section is the family of
rotations: `L_{z x₀⁻¹}` is the rotation by the angle from `x₀` to `z`.

## Main definitions

* `Diffeomorph.smulContinuousMonoidHom`: a `C^n` action of a Lie group on a compact manifold, as a
  continuous homomorphism into the diffeomorphism group.
* `TauCeti.Lie.leftTranslationSection`: the section `z ↦ L_{z x₀⁻¹}` of evaluation at `x₀`.
* `TauCeti.Lie.diffeomorphHomeomorphProdStabilizer`: the trivialization
  `Diff(G) ≃ₜ G × Diff(G, x₀)` of evaluation at `x₀`.

## References

* R. Palais, *Local triviality of the restriction map for embeddings*, Comment. Math. Helv. 34
  (1960), 305–312.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Example 6.30, on compact Lie
  groups covered by their translations.
-/

public section

noncomputable section

open MulAction
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [CompactSpace M]
  [IsManifold I n G] [IsManifold I' n M] [MulAction G M] [ContMDiffSMul I I' n G M]

variable (I I' n G M) in
/-- **A smooth action is a continuous homomorphism into the diffeomorphism group.** A `C^n` action
of a group `G`, modelled on `I`, on a compact `C^n` manifold `M` sends `g` to the diffeomorphism
`x ↦ g • x` of `M`. This is a homomorphism `G →* Diff(M)`, and it is continuous for the weak Whitney
topology on `Diff(M)`, since the family `(g, x) ↦ g • x` is jointly `C^n`. -/
def smulContinuousMonoidHom : G →ₜ* (M ≃ₘ^n⟮I', I'⟯ M) where
  toFun g := Diffeomorph.smul I I' n g
  map_one' := Diffeomorph.ext fun x ↦ one_smul G x
  map_mul' g h := Diffeomorph.ext fun x ↦ mul_smul g h x
  continuous_toFun := ContMDiff.continuous_diffeomorphWeakWhitney (I' := I)
    (f := fun g ↦ Diffeomorph.smul I I' n g) contMDiff_smul

@[simp]
theorem smulContinuousMonoidHom_apply_apply (g : G) (x : M) :
    smulContinuousMonoidHom I I' n G M g x = g • x :=
  (rfl)

end Diffeomorph

namespace TauCeti.Lie

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CompactSpace G] [Group G]
  [LieGroup I n G]

variable (I n) in
/-- **The left-translation section of evaluation.** For a point `x₀` of a compact `C^n` Lie group
`G`, the left translations `z ↦ L_{z x₀⁻¹}` form a continuous map `G → Diff(G)` sending `z` to a
diffeomorphism taking `x₀` to `z` (`TauCeti.Lie.leftTranslationSection_apply_self`): a section of
evaluation `Diff(G) → G` at `x₀`, defined on all of `G`. -/
def leftTranslationSection (x₀ : G) : C(G, G ≃ₘ^n⟮I, I⟯ G) :=
  (Diffeomorph.smulContinuousMonoidHom I I n G G : C(G, G ≃ₘ^n⟮I, I⟯ G)).comp
    ⟨(· * x₀⁻¹), (contMDiff_mul_right (I := I) (n := n)).continuous⟩

@[simp]
theorem leftTranslationSection_apply_apply (x₀ z x : G) :
    leftTranslationSection I n x₀ z x = z * x₀⁻¹ * x :=
  (rfl)

/-- The left-translation section of evaluation at `x₀` takes `x₀` to the prescribed point. -/
theorem leftTranslationSection_apply_self (x₀ z : G) : leftTranslationSection I n x₀ z x₀ = z := by
  simp

/-- The left-translation section of evaluation at `x₀` passes through the identity at `x₀`. -/
@[simp]
theorem leftTranslationSection_self (x₀ : G) : leftTranslationSection I n x₀ x₀ = 1 :=
  Diffeomorph.ext fun x ↦ by simp

variable [T2Space G] [LocallyCompactSpace E]

variable (I n) in
/-- **Evaluation on the diffeomorphism group of a compact Lie group is a trivial bundle.** For a
compact Hausdorff `C^n` Lie group `G` with locally compact model space and a point `x₀ : G`, the map
`g ↦ (g x₀, L_{g(x₀) x₀⁻¹}⁻¹ * g)` is a homeomorphism from `Diff(G)`, with the weak Whitney
topology, onto `G × Diff(G, x₀)`, with `Diff(G, x₀)` the stabilizer of `x₀`. Its first coordinate
is evaluation at `x₀`, and its inverse sends `(z, h)` to `L_{z x₀⁻¹} * h`
(`TauCeti.Lie.diffeomorphHomeomorphProdStabilizer_symm_apply`). -/
def diffeomorphHomeomorphProdStabilizer (x₀ : G) :
    (G ≃ₘ^n⟮I, I⟯ G) ≃ₜ G × stabilizer (G ≃ₘ^n⟮I, I⟯ G) x₀ :=
  orbitMapHomeomorph x₀ (Diffeomorph.continuous_eval_const x₀) (leftTranslationSection I n x₀)
    (map_continuous _) (leftTranslationSection_apply_self x₀)

@[simp]
theorem diffeomorphHomeomorphProdStabilizer_apply_fst (x₀ : G) (g : G ≃ₘ^n⟮I, I⟯ G) :
    (diffeomorphHomeomorphProdStabilizer I n x₀ g).1 = g x₀ :=
  orbitMapHomeomorph_apply_fst g

@[simp]
theorem coe_diffeomorphHomeomorphProdStabilizer_apply_snd (x₀ : G) (g : G ≃ₘ^n⟮I, I⟯ G) :
    ((diffeomorphHomeomorphProdStabilizer I n x₀ g).2 : G ≃ₘ^n⟮I, I⟯ G) =
      (leftTranslationSection I n x₀ (g x₀))⁻¹ * g :=
  coe_orbitMapHomeomorph_apply_snd g

@[simp]
theorem diffeomorphHomeomorphProdStabilizer_symm_apply (x₀ : G)
    (p : G × stabilizer (G ≃ₘ^n⟮I, I⟯ G) x₀) :
    (diffeomorphHomeomorphProdStabilizer I n x₀).symm p = leftTranslationSection I n x₀ p.1 * p.2 :=
  orbitMapHomeomorph_symm_apply p

end TauCeti.Lie
