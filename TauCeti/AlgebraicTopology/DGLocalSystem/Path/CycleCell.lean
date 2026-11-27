/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Augmentation
public import TauCeti.AlgebraicTopology.DGLocalSystem.CellResolution
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel.Basic

/-!
# Brown models of one cell attached along a cycle

For an `n`-cycle `x` of the chains `C_*(Ω_b B; R)` on the Moore loops at `b`, the free module

`K = C_*(Ω_b B; R) e₀ ⊕ C_*(Ω_b B; R) e₁`,  `D e₀ = 0`,  `D e₁ = x e₀`

of `TauCeti.cycleCellCocycle R n x` is Brown's twisted tensor product of a complex with one `0`-cell
at `b` and one `(n + 1)`-cell attached along `x`. Brown's construction compares it with the chains
`C_*(P_b B; R)` on the Moore paths from `b`, a differential graded left module over
`C_*(Ω_b B; R)` through concatenation in front (`TauCeti.pathFromChain_isDGLeftModule`), by a map
linear over the loop chains: the generator `e₀` goes to the point chain `[b]` of the constant path,
and the generator `e₁` to an `(n + 1)`-chain `c` of paths bounding the image `x · [b]` of its
attaching row. This file constructs that comparison for any such chain `c`
(`TauCeti.cycleCellPathComparison`), shows that it commutes with the differentials
(`TauCeti.cycleCellPathComparison_differential`) and with the augmentations
(`TauCeti.cubicalChainModuleAugmentation_cycleCellPathComparison`), and that it is a
quasi-isomorphism as soon as `K` resolves `R`
(`TauCeti.exists_cycleCellCocycle_differential_eq_and_cycleCellPathComparison_add_eq`): both
augmentations are then quasi-isomorphisms onto `R`, the based path space being contractible. So
`K` with this comparison is a Brown model (`TauCeti.cycleCellBrownModel`).

The circle (`TauCeti.loopCellBrownModel`) and the spheres (`TauCeti.sphereBrownModel`) are the
instances of this construction.

## Main definitions

* `TauCeti.cycleCellPathComparison`: the map `K → C_*(P_b B; R)`, `e₀ ↦ [b]`, `e₁ ↦ c`.
* `TauCeti.cycleCellBrownModel`: `K` with this comparison, as a Brown model, when `K` resolves `R`.

## Main results

* `TauCeti.cycleCellPathComparison_differential`: the comparison commutes with the differentials.
* `TauCeti.exists_cycleCellCocycle_differential_eq_and_cycleCellPathComparison_add_eq`: when `K`
  resolves `R`, the comparison is a quasi-isomorphism.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open AlgebraicTopology

namespace TauCeti

/-! ### The comparison of one cell attached along a cycle -/

section Comparison

variable {B : Type*} [TopologicalSpace B] {b : B} (H : Type*) (R : Type*) [CommRing R]

/-- **The comparison of a cell attached along a cycle with the chains on the based paths**: the
map from the free module on the generators `e₀ = Sum.inl ()` and `e₁ = Sum.inr ()` to
`C_*(P_b B; R)`, linear over the loop algebra `C_*(Ω_b B; R)`, sending `e₀` to the point chain
`[b]` of the constant path and `e₁` to the chain `c`. It commutes with the differentials of
`TauCeti.cycleCellCocycle R n x` when `c` bounds `x · [b]`
(`TauCeti.cycleCellPathComparison_differential`). -/
def cycleCellPathComparison (c : cubicalChainModule (MoorePathFrom B b) H R) :
    (Unit ⊕ Unit →₀ loopChainAlgebra B b R) →ₗ[loopChainAlgebra B b R]
      cubicalChainModule (MoorePathFrom B b) H R :=
  Finsupp.linearCombination _
    (Sum.elim (fun _ ↦ cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b))
      (fun _ ↦ c))

variable {H R}

@[simp]
theorem cycleCellPathComparison_single_inl (c : cubicalChainModule (MoorePathFrom B b) H R)
    (α : loopChainAlgebra B b R) :
    cycleCellPathComparison H R c (Finsupp.single (Sum.inl ()) α) =
      α • cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) := by
  simp [cycleCellPathComparison]

@[simp]
theorem cycleCellPathComparison_single_inr (c : cubicalChainModule (MoorePathFrom B b) H R)
    (β : loopChainAlgebra B b R) :
    cycleCellPathComparison H R c (Finsupp.single (Sum.inr ()) β) = β • c := by
  simp [cycleCellPathComparison]

/-- The comparison on `α e₀ + β e₁` is `α · [b] + β · c`. -/
theorem cycleCellPathComparison_apply (c : cubicalChainModule (MoorePathFrom B b) H R)
    (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    cycleCellPathComparison H R c u =
      u (Sum.inl ()) •
          cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) +
        u (Sum.inr ()) • c := by
  have hu : u = Finsupp.single (Sum.inl ()) (u (Sum.inl ())) +
      Finsupp.single (Sum.inr ()) (u (Sum.inr ())) := by
    ext i
    rcases i with ⟨⟩ | ⟨⟩ <;> simp
  conv_lhs => rw [hu]
  rw [map_add, cycleCellPathComparison_single_inl, cycleCellPathComparison_single_inr]

variable {n : ℕ} {x : loopChainAlgebra B b R}
  {hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ))}
  {hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0}
  {c : cubicalChainModule (MoorePathFrom B b) H R}

/-- **The comparison commutes with the differentials** as soon as the image `c` of `e₁` bounds the
image `x · [b]` of its attaching row. -/
theorem cycleCellPathComparison_differential
    (hc : cubicalChainModuleDifferential (MoorePathFrom B b) H R c =
      x • cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b))
    (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    cycleCellPathComparison H R c
        (rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
          u) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R (cycleCellPathComparison H R c u) := by
  refine ((forall_linearCombination_rowFiniteTwistedDifferential_iff
    (pathFromChain_isDGLeftModule B b H R) _ _).2 ?_) u
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · simp
  · simp [hc]

/-- **The comparison commutes with the augmentations** when `c` has positive dimension: the
augmentation of the image of `u` in `C_*(P_b B; R)` is the augmentation of the coefficient of
`e₀`. -/
theorem cubicalChainModuleAugmentation_cycleCellPathComparison
    (hc : c ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-((n : ℤ) + 1)))
    (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    cubicalChainModuleAugmentation (MoorePathFrom B b) H R (cycleCellPathComparison H R c u) =
      loopCellAugmentation B b R u := by
  have hc0 : cubicalChainModuleAugmentation (MoorePathFrom B b) H R c = 0 :=
    ((mem_trivialGrading_iff R R).1 (cubicalChainModuleAugmentation_mem hc)).resolve_left (by omega)
  simp [cycleCellPathComparison_apply, pathFromChainAugmentation_smul, loopCellAugmentation_apply,
    hc0]

end Comparison

section QuasiIso

variable {B : Type*} [TopologicalSpace B] {b : B} {H : Type*} {R : Type*} [CommRing R] {n : ℕ}
  {x : loopChainAlgebra B b R} {hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ))}
  {hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0}
  {c : cubicalChainModule (MoorePathFrom B b) H R}

/-- **Brown's resolution of one cell attached along a cycle is quasi-isomorphic to the chains on
the based paths.** Let the free module `K` of `TauCeti.cycleCellCocycle R n x` resolve `R`: every
cycle of `K` whose augmentation vanishes is a boundary, as for a sphere
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). Let `c` be an
`(n + 1)`-chain of paths bounding `x · [b]`. Then the comparison
`TauCeti.cycleCellPathComparison` from `K` to `C_*(P_b B; R)` is a quasi-isomorphism: every
relative cycle `(u, w)`, with `D u = 0` and `g(u) = d w`, is a relative boundary
`(D u', g(u') + d w')`. -/
theorem exists_cycleCellCocycle_differential_eq_and_cycleCellPathComparison_add_eq
    (hcm : c ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-((n : ℤ) + 1)))
    (hc : cubicalChainModuleDifferential (MoorePathFrom B b) H R c =
      x • cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b))
    (hK : ∀ {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R},
      rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
          u = 0 →
      loopCellAugmentation B b R u = 0 →
      ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
          v = u)
    {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R} {w : cubicalChainModule (MoorePathFrom B b) H R}
    (hu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
        u = 0)
    (hw : cycleCellPathComparison H R c u = cubicalChainModuleDifferential _ H R w) :
    ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
          u' = u ∧
      cycleCellPathComparison H R c u' + cubicalChainModuleDifferential _ H R w' = w :=
  -- Both augmentations are quasi-isomorphisms onto `R`, the comparison commutes with them, and
  -- `e₀` is a cycle of augmentation `1`.
  exists_differential_eq_and_add_eq_of_augmentation
    (f := (cycleCellPathComparison H R c).restrictScalars R)
    (cycleCellPathComparison_differential hc)
    (cubicalChainModuleAugmentation_cycleCellPathComparison hcm)
    (cubicalChainModuleAugmentation_differential (G := H))
    (cycleCellCocycle_differential_single_inl_one hx hdx) (by simp) hK
    exists_pathFromChainDifferential_eq_of_augmentation_eq_zero hu hw

end QuasiIso

section Model

variable {B : Type*} [TopologicalSpace B] {b : B} (H : Type*) {R : Type*} [CommRing R] {n : ℕ}
  {x : loopChainAlgebra B b R}

/-- **One cell attached along a cycle, as a Brown model.** Let the free module `K` of
`TauCeti.cycleCellCocycle R n x` resolve `R`: every cycle of `K` whose augmentation vanishes is a
boundary. Then `K`, with the comparison `TauCeti.cycleCellPathComparison` sending `e₀` to the point
chain `[b]` and `e₁` to an `(n + 1)`-chain `c` of paths bounding `x · [b]`, is a Brown model of
`C_*(P_b B; R)`. -/
def cycleCellBrownModel (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
    (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0)
    (c : cubicalChainModule (MoorePathFrom B b) H R)
    (hcm : c ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-((n : ℤ) + 1)))
    (hc : cubicalChainModuleDifferential (MoorePathFrom B b) H R c =
      x • cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b))
    (hK : ∀ {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R},
      rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
          u = 0 →
      loopCellAugmentation B b R u = 0 →
      ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
          v = u) :
    BrownModel B b H R (Unit ⊕ Unit) (Sum.elim (fun _ ↦ 0) (fun _ ↦ (n : ℤ) + 1)) where
  cocycle := cycleCellCocycle R n x hx hdx
  wellFounded := wellFounded_mem_support_cycleCellCocycle hx hdx
  comparison := Sum.elim
    (fun _ ↦ cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b))
    (fun _ ↦ c)
  comparison_mem := by
    rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    · simpa using cubicalChainModulePoint_mem (G := H) (R := R) (MoorePathFrom.refl B b)
    · simpa using hcm
  -- `cycleCellPathComparison` is by definition the linear combination of these images.
  linearCombination_comparison_m := (forall_linearCombination_rowFiniteTwistedDifferential_iff
    (pathFromChain_isDGLeftModule B b H R) _ _).1 (cycleCellPathComparison_differential hc)
  exists_differential_eq_and_linearCombination_add_eq _ _ hu hw :=
    exists_cycleCellCocycle_differential_eq_and_cycleCellPathComparison_add_eq hcm hc hK hu hw

variable {H} {hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ))}
  {hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0}
  {c : cubicalChainModule (MoorePathFrom B b) H R}

/-- The cocycle of the Brown model of a cell attached along `x` is `TauCeti.cycleCellCocycle`. -/
@[simp]
theorem cycleCellBrownModel_cocycle (hcm hc hK) :
    (cycleCellBrownModel H hx hdx c hcm hc hK).cocycle = cycleCellCocycle R n x hx hdx := (rfl)

/-- The Brown model of a cell attached along `x` sends the generator `e₀` of the `0`-cell to the
point chain `[b]` of the constant path. -/
@[simp]
theorem cycleCellBrownModel_comparison_inl (hcm hc hK) (y : Unit) :
    (cycleCellBrownModel H hx hdx c hcm hc hK).comparison (Sum.inl y) =
      cubicalChainModulePoint (MoorePathFrom B b) H R (MoorePathFrom.refl B b) := (rfl)

/-- The Brown model of a cell attached along `x` sends the generator `e₁` of the cell to `c`. -/
@[simp]
theorem cycleCellBrownModel_comparison_inr (hcm hc hK) (y : Unit) :
    (cycleCellBrownModel H hx hdx c hcm hc hK).comparison (Sum.inr y) = c := (rfl)

/-- The comparison of the Brown model of a cell attached along `x` is
`TauCeti.cycleCellPathComparison`. -/
@[simp]
theorem linearCombination_cycleCellBrownModel_comparison (hcm hc hK) :
    Finsupp.linearCombination (loopChainAlgebra B b R)
        (cycleCellBrownModel H hx hdx c hcm hc hK).comparison =
      cycleCellPathComparison H R c := (rfl)

end Model

end TauCeti
