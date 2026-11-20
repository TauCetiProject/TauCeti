/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
public import TauCeti.Topology.MappingSpace.Fibration
public import TauCeti.Topology.MappingSpace.Sphere.Moore

/-!
# Sphere maps sending the base point into a highly connected subspace

Let `Q` be a space, `Y ⊆ Q` a subspace and `y ∈ Y`. Among the maps `Sᵏ → Q` of a sphere, those
sending the base point `s₀` to `y` form the based mapping space `Map_*(Sᵏ, Q)`, a copy of the
iterated loop space `Ωᵏ_y Q`, and those sending `s₀` into `Y` form the preimage `ev⁻¹(Y)` of `Y`
under evaluation at `s₀`. Evaluation `ev⁻¹(Y) → Y` is a Serre fibration with fibre `Map_*(Sᵏ, Q)`
over `y`, so when `Y` is highly connected the fibre carries the homology of the total space in low
degrees: if `π_j(Y, y)` is trivial for every `j ≤ n`, the inclusion
`Map_*(Sᵏ, Q) → ev⁻¹(Y)` induces isomorphisms on `H_m` for `m < n` and surjections for `m ≤ n`
(`TauCeti.isIso_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere`,
`TauCeti.epi_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere`).

The same holds for the Moore model of these spaces, used for the DG local system of the
evaluation fibration `Map(S², Q) → Q`: the space `P_{Q→Y} 𝓛₀Q` of Moore paths of contractible
free loops starting at a constant loop and ending at a constant loop at a point of `Y`, projecting
to that point, with fibre `P_{Q→y} 𝓛₀Q` over `y`. It is fibre homotopy equivalent over `Q` to the
space of maps `S² → Q` with evaluation at the south pole
(`TauCeti.sphere2SouthFiberHomotopyEquivMoorePaths`), so the inclusion
`P_{Q→y} 𝓛₀Q → P_{Q→Y} 𝓛₀Q` is again an isomorphism on `H_m` for `m < n`
(`TauCeti.isIso_singularHomologyMap_preimageInclusion_constContractibleMoorePaths`) and onto for
`m ≤ n` (`TauCeti.epi_singularHomologyMap_preimageInclusion_constContractibleMoorePaths`). The Moore
paths themselves need not form a Serre fibration over `Q`: the comparison only uses the fibre
homotopy invariance of the statement
(`TauCeti.FiberHomotopyEquiv.isIso_singularHomologyMap_preimageInclusion_iff`).

For `Y` a `(d + 1)`-connected closed submanifold of a closed manifold `Q`, this is the comparison
in the proof of Lemma 7.7 of Barraud, Damian, Humilière and Oancea: the inclusion of the fibre
`Ω²Q ≃ P_{Q→y} 𝓛₀Q` into `P_{Q→Y} 𝓛₀Q` is an isomorphism on homology in degrees `≤ d`, which their
argument reads off the Serre spectral sequence of `P_{Q→Y} 𝓛₀Q → Y`. Here it follows from the
exact homotopy sequence of the evaluation fibration instead
(`TauCeti.TopCat.isIso_singularHomologyMap_preimageInclusion`). Their Lemma 7.7 is one of the
inputs of Theorem 7.1 on hypersurfaces of cotangent bundles knotted with a sphere.

## Main results

* `TauCeti.isIso_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere`,
  `TauCeti.epi_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere`: the based maps of a
  sphere among the maps sending the base point into an `n`-connected subspace.
* `TauCeti.isIso_singularHomologyMap_preimageInclusion_constContractibleMoorePaths`,
  `TauCeti.epi_singularHomologyMap_preimageInclusion_constContractibleMoorePaths`: the inclusion
  `P_{Q→y} 𝓛₀Q → P_{Q→Y} 𝓛₀Q` over an `n`-connected subspace.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemma 7.7.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Proposition 4.21.
-/

public section

open CategoryTheory AlgebraicTopology Metric
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

variable (R : Type u) [Ring R] {Q : Type u} [TopologicalSpace Q] {Y : Set Q} {y : Q} {n : ℕ}

/-! ### Maps of a sphere -/

section Sphere

variable {k : ℕ} (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

/-- **Based maps of a sphere among the maps sending the base point into a highly connected
subspace.** If `π_j(Y, y)` is trivial for every `j ≤ n`, the inclusion of the based maps
`Map_*(Sᵏ, Q) = ev⁻¹(y)` into the maps `ev⁻¹(Y)` sending the base point `s₀` into `Y` induces
isomorphisms `H_m(Map_*(Sᵏ, Q); R) → H_m(ev⁻¹(Y); R)` for every `m < n`. -/
theorem isIso_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere (hy : y ∈ Y)
    (hY : ∀ j ≤ n, Subsingleton (π_ j Y ⟨y, hy⟩)) {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      ((mappingSpaceEval (X := Q) s₀).preimageInclusion hy)) :=
  TopCat.isIso_singularHomologyMap_preimageInclusion R
    (mem_serreFibrations_restrictPreimage_mappingSpaceEval_sphere s₀ Y) hy hY hm

/-- **Based maps of a sphere among the maps sending the base point into a highly connected
subspace, in the top degree.** If `π_j(Y, y)` is trivial for every `j ≤ n`, the inclusion of the
based maps `Map_*(Sᵏ, Q) = ev⁻¹(y)` into the maps `ev⁻¹(Y)` sending the base point `s₀` into `Y`
induces surjections `H_m(Map_*(Sᵏ, Q); R) → H_m(ev⁻¹(Y); R)` for every `m ≤ n`. -/
theorem epi_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere (hy : y ∈ Y)
    (hY : ∀ j ≤ n, Subsingleton (π_ j Y ⟨y, hy⟩)) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      ((mappingSpaceEval (X := Q) s₀).preimageInclusion hy)) :=
  TopCat.epi_singularHomologyMap_preimageInclusion R
    (mem_serreFibrations_restrictPreimage_mappingSpaceEval_sphere s₀ Y) hy hY hm

end Sphere

/-! ### Moore paths of contractible free loops -/

section Moore

/-- **The Moore paths `P_{Q→y} 𝓛₀Q` among `P_{Q→Y} 𝓛₀Q` over a highly connected subspace.** Let
`P_{Q→Y} 𝓛₀Q` be the Moore paths of contractible free loops of `Q` from a constant loop to a
constant loop at a point of `Y`. If `π_j(Y, y)` is trivial for every `j ≤ n`, the inclusion of the
paths ending at the constant loop at `y` induces isomorphisms
`H_m(P_{Q→y} 𝓛₀Q; R) → H_m(P_{Q→Y} 𝓛₀Q; R)` for every `m < n`. -/
theorem isIso_singularHomologyMap_preimageInclusion_constContractibleMoorePaths (hy : y ∈ Y)
    (hY : ∀ j ≤ n, Subsingleton (π_ j Y ⟨y, hy⟩)) {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      ((ContinuousMap.snd.comp (constContractibleMooreEndpoints Q)).preimageInclusion hy)) :=
  ((sphere2SouthFiberHomotopyEquivMoorePaths Q).isIso_singularHomologyMap_preimageInclusion_iff
    R hy m).2
    (isIso_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere R Sphere2.south hy hY hm)

/-- **The Moore paths `P_{Q→y} 𝓛₀Q` among `P_{Q→Y} 𝓛₀Q` over a highly connected subspace, in the
top degree.** If `π_j(Y, y)` is trivial for every `j ≤ n`, the inclusion of the Moore paths of
contractible free loops ending at the constant loop at `y` into those ending at a constant loop at a
point of `Y` induces surjections `H_m(P_{Q→y} 𝓛₀Q; R) → H_m(P_{Q→Y} 𝓛₀Q; R)` for every `m ≤ n`. -/
theorem epi_singularHomologyMap_preimageInclusion_constContractibleMoorePaths (hy : y ∈ Y)
    (hY : ∀ j ≤ n, Subsingleton (π_ j Y ⟨y, hy⟩)) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      ((ContinuousMap.snd.comp (constContractibleMooreEndpoints Q)).preimageInclusion hy)) :=
  ((sphere2SouthFiberHomotopyEquivMoorePaths Q).epi_singularHomologyMap_preimageInclusion_iff
    R hy m).2
    (epi_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere R Sphere2.south hy hY hm)

end Moore

end TauCeti
