/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
public import TauCeti.Topology.MappingSpace.Based
public import TauCeti.Topology.MappingSpace.Evaluation

/-!
# Based maps inside the maps sending the base point into a highly connected subspace

Let `B` be a space with a base point `b₀` and let `Y` be a subspace of a space `Q`. The maps
`B → Q` sending `b₀` into `Y` form the preimage `ev⁻¹(Y)` of `Y` under evaluation
`ev : Map(B, Q) → Q` at `b₀`. For `q ∈ Y`, the based maps `Map_*(B, Q)` sending `b₀` to `q` are
the fibre of the restricted evaluation `ev⁻¹(Y) → Y` over `q`, and include into `ev⁻¹(Y)`
(`TauCeti.BasedMap.inclEvalPreimage`).

If evaluation is a Serre fibration, as it is for spheres
(`TauCeti.isHurewiczFibration_mappingSpaceEval_sphere`), so is its restriction over `Y`
(`TauCeti.TopCat.mem_serreFibrations_restrictPreimage`). When `Y` is `n`-connected at `q`, the
inclusion of this fibre is then an isomorphism on singular homology below degree `n`
(`TauCeti.BasedMap.bijective_singularHomologyMap_inclEvalPreimage`), by the exact homotopy sequence
(`TauCeti.TopCat.isIso_singularHomologyMap_fiberι`).

For `B = S²` the based maps are a model of the double loop space `Ω²Q`, and `ev⁻¹(Y)` is one of
the space `P_{Q→Y} 𝓛₀Q` of paths of free loops from a constant loop to a constant loop at a
point of `Y`, by reading `S²` as the suspension of the circle. Barraud, Damian, Humilière and
Oancea use this comparison in the proof of their Lemma 7.7, where `Y` is a highly connected
submanifold of `Q`: there it is read off the Serre spectral sequence of `P_{Q→Y} 𝓛₀Q → Y`.

## Main declarations

* `TauCeti.BasedMap.inclEvalPreimage`: the based maps at `q ∈ Y` as maps sending `b₀` into `Y`.
* `TauCeti.BasedMap.bijective_singularHomologyMap_inclEvalPreimage`: over an `n`-connected `Y`,
  this inclusion is bijective on `H_m` for `m < n`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, proof of Lemma 7.7.
* A. Hatcher, *Algebraic Topology*, Theorem 4.41 and Proposition 4.21.
-/

public section

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.BasedMap

variable {B Q : Type u} [TopologicalSpace B] [TopologicalSpace Q] {b₀ : B} {Y : Set Q} {q : Q}

/-- The based maps sending `b₀` to a point `q` of `Y`, as maps sending `b₀` into `Y`: the
inclusion of the fibre over `q` of evaluation `ev⁻¹(Y) → Y` at `b₀`. -/
def inclEvalPreimage (hq : q ∈ Y) :
    C(BasedMap B Q b₀ q, mappingSpaceEval (X := Q) b₀ ⁻¹' Y) :=
  ⟨fun f ↦ ⟨f.1, by simpa [f.2] using hq⟩, by fun_prop⟩

@[simp]
theorem coe_inclEvalPreimage_apply (hq : q ∈ Y) (f : BasedMap B Q b₀ q) :
    (inclEvalPreimage hq f : C(B, Q)) = f.1 :=
  (rfl)

/-- **Based maps over a highly connected subspace.** Suppose that evaluation
`Map(B, Q) → Q` at `b₀` is a Serre fibration, and that `πₖ(Y, q)` is trivial for every `k ≤ n`.
Then the inclusion of the based maps `Map_*(B, Q)` at `q` into the maps sending `b₀` into `Y` is
bijective on `H_m(-; R)` for every `m < n`. -/
theorem bijective_singularHomologyMap_inclEvalPreimage
    (hev : TopCat.serreFibrations (TopCat.ofHom (mappingSpaceEval (X := Q) b₀))) (hq : q ∈ Y)
    {n : ℕ} (hY : ∀ k ≤ n, Subsingleton (π_ k Y ⟨q, hq⟩)) (R : Type u) [Ring R] {m : ℕ}
    (hm : m < n) :
    Function.Bijective
      (ContinuousMap.singularHomologyMap R m (inclEvalPreimage (b₀ := b₀) hq)) := by
  -- The restriction `ev⁻¹(Y) → Y` of evaluation is a Serre fibration.
  let p : TopCat.of (mappingSpaceEval (X := Q) b₀ ⁻¹' Y) ⟶ TopCat.of Y :=
    TopCat.ofHom ((mappingSpaceEval (X := Q) b₀).restrictPreimage Y)
  have hp : TopCat.serreFibrations p := TopCat.mem_serreFibrations_restrictPreimage hev Y
  -- The based maps are its fibre over `q`.
  let e : BasedMap B Q b₀ q ≃ₜ p.fiber ⟨q, hq⟩ :=
    { toFun f := ⟨inclEvalPreimage hq f, Subtype.ext (by simp [p, f.2])⟩
      invFun g := ⟨g.1.1, by simpa [p] using congrArg Subtype.val g.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hcomp : inclEvalPreimage (b₀ := b₀) hq = (p.fiberι ⟨q, hq⟩).hom.comp e :=
    ContinuousMap.ext fun f ↦ (TopCat.Hom.fiberι_apply p _ (e f)).symm
  -- The fibre inclusion is a homology isomorphism, and `e` is a homeomorphism.
  have hι : Function.Bijective
      (ContinuousMap.singularHomologyMap R m (p.fiberι ⟨q, hq⟩).hom) := by
    have := TopCat.isIso_singularHomologyMap_fiberι R hp hY hm
    exact ConcreteCategory.bijective_of_isIso
      (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (p.fiberι ⟨q, hq⟩))
  have hcomp' : ⇑(ContinuousMap.singularHomologyMap R m (inclEvalPreimage (b₀ := b₀) hq)) =
      ContinuousMap.singularHomologyMap R m (p.fiberι ⟨q, hq⟩).hom ∘
        ContinuousMap.singularHomologyMap R m (e : C(BasedMap B Q b₀ q, p.fiber ⟨q, hq⟩)) := by
    funext z
    rw [hcomp, Function.comp_apply, ContinuousMap.singularHomologyMap_comp]
  rw [hcomp']
  exact hι.comp (e.toHomotopyEquiv.bijective_singularHomologyMap R m)

end TauCeti.BasedMap
