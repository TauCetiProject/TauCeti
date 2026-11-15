/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Pullback
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Kunneth
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule

/-!
# The based path fibration over a cubical cell

Let `f : Iᵐ⁺¹ → X` be a cubical cell of a space `X` with base point `b`, and let `τ v` be a
continuous family of Moore paths from `b` to `f v`, for instance the radial paths of a
characteristic map (`TauCeti.MoorePathPullback.radialPaths`). The pullback `f*P_b X` of the based
Moore path fibration along `f` is trivialized by `τ` up to fibre homotopy
(`TauCeti.MoorePathPullback.fiberHomotopyEquiv`). Reading the trivialization with the loop
coordinate first gives the **cell map**

`F : Ω_b X × Iᵐ⁺¹ → f*P_b X`, `(ω, v) ↦ (v, ω ⋆ τ v)`

(`TauCeti.MoorePathPullback.cellMap`), which is equivariant for left concatenation of loops. This
file proves the two facts that make the chains of `f*P_b X` over the cell, relative to its boundary,
quasi-isomorphic, linearly over the loop chains `C_*(Ω_b X; k)`, to the free module of rank one on a
generator of degree `m + 1`:

* **Homology.** Taking the cross product with the fundamental cycle `[Iᵐ⁺¹]` and pushing forward
  along `F` is an isomorphism
  `H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f*P_b X, f*P_b X|_{∂Iᵐ⁺¹}; k)`
  over every commutative ring `k` (`TauCeti.MoorePathPullback.cellHomologyEquiv`), sending the
  class of a cycle `z` to the class of the relative cycle `F_*(z × [Iᵐ⁺¹])`
  (`TauCeti.MoorePathPullback.cellHomologyEquiv_homologyπ`). It is the relative Künneth
  isomorphism for the cube pair (`TauCeti.cubicalHomologyCubeBoundaryPairProdLeftEquiv`), followed
  by the relative chain homotopy equivalence of the trivialization.
* **Linearity.** On chains, `c ↦ F_*(c × [Iᵐ⁺¹])` (`TauCeti.MoorePathPullback.cellChain`) is linear
  over the left action of `C_*(Ω_b X; k)` by concatenation in front
  (`TauCeti.MoorePathPullback.leftAct_cellChain`). So for the generator
  `c_f = F_*([1] × [Iᵐ⁺¹])`, the cube `v ↦ F (1, v)` (`TauCeti.MoorePathPullback.cellGenerator`),
  the action `a ↦ a · c_f` is `a ↦ F_*(a × [Iᵐ⁺¹])`, up to reindexing the degree
  (`TauCeti.MoorePathPullback.leftAct_cellGenerator`).

Together, `a ↦ a · c_f` induces, up to that reindexing, an isomorphism from `H_q(Ω_b X)` onto the
relative homology of the cell in degree `q + m + 1`. This is the cell-by-cell input
of Brown's twisted tensor product, the semi-free resolution of the ground ring over the chains on
the loop space of a CW complex: the generator of a cell is attached and sent to `c_f`
(`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`).

The cube is the second factor of the cross product, so that the left action of the loop chains
acts on the first coordinates of `F_*(c × [Iᵐ⁺¹])`; with the cube first, the two cross products
`a × ([Iᵐ⁺¹] × c)` and `[Iᵐ⁺¹] × (a c)` would differ by a permutation of coordinates.

## Main definitions

* `TauCeti.MoorePathPullback.cellMap`: the cell map `(ω, v) ↦ (v, ω ⋆ τ v)`.
* `TauCeti.MoorePathPullback.cellChain`: the chain map `c ↦ F_*(c × [Iᵐ⁺¹])`.
* `TauCeti.MoorePathPullback.cellGenerator`: the generator `F_*([1] × [Iᵐ⁺¹])`.
* `TauCeti.MoorePathPullback.cellHomologyEquiv`: the isomorphism
  `H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f*P_b X, f*P_b X|_{∂Iᵐ⁺¹}; k)`.

## Main results

* `TauCeti.MoorePathPullback.cellHomologyEquiv_homologyπ`: the isomorphism on cycles.
* `TauCeti.MoorePathPullback.leftAct_cellChain`,
  `TauCeti.MoorePathPullback.leftAct_cellGenerator`: linearity over the loop chains.

The cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)` and the relative Künneth theorem behind
`TauCeti.cubicalHomologyCubeBoundaryPairProdLeftEquiv` live in universe `0`, so the space `X` and
the coefficient ring `k` do too.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential
  graded coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3–4 and §7.1.
-/

public noncomputable section

open CategoryTheory HomologicalComplex ContinuousMap
open scoped unitInterval Topology

namespace TauCeti.MoorePathPullback

variable {X : Type} [TopologicalSpace X] {m : ℕ}

/-- The pair `(f*P_b X, f*P_b X|_{∂Iᵐ⁺¹})` of the based path fibration pulled back along a cubical
cell `f`, relative to the part over the boundary of the cube. -/
abbrev cellPair (f : C(ULift.{0} (I^(Fin (m + 1))), X)) (b : X) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
    ((proj f b) ⁻¹' (ULift.down ⁻¹' Cube.boundary (Fin (m + 1))))

variable {b : X} {f : C(ULift.{0} (I^(Fin (m + 1))), X)}
  (τ : C(ULift.{0} (I^(Fin (m + 1))), MoorePath X)) (h₀ : ∀ v, (τ v).source = b)
  (h₁ : ∀ v, (τ v).target = f v) (k : Type) [CommRing k]

/-! ### The cell map and its chains -/

/-- The cell map `Ω_b X × Iᵐ⁺¹ → f*P_b X`, `(ω, v) ↦ (v, ω ⋆ τ v)`: the trivialization of the
pulled-back path fibration, with the loop coordinate first. -/
def cellMap : C(MooreLoopSpace X b × ULift.{0} (I^(Fin (m + 1))), MoorePathPullback f b) :=
  (trivializationMap τ h₀ h₁).comp ⟨Prod.swap, continuous_swap⟩

@[simp]
theorem cellMap_apply (x : MooreLoopSpace X b × ULift.{0} (I^(Fin (m + 1)))) :
    cellMap τ h₀ h₁ x = trivializationMap τ h₀ h₁ (x.2, x.1) :=
  (rfl)

/-- The cell map is equivariant for left concatenation of loops. -/
theorem cellMap_mul (ω η : MooreLoopSpace X b) (v : ULift.{0} (I^(Fin (m + 1)))) :
    cellMap τ h₀ h₁ (ω * η, v) = ω • cellMap τ h₀ h₁ (η, v) :=
  trivializationMap_mul τ h₀ h₁ v ω η

/-- The chain map `c ↦ F_*(c × [Iᵐ⁺¹])` from the chains of the based loop space to those of the
pulled-back path fibration, for the cell map `F` and the identity cube `[Iᵐ⁺¹]`. -/
def cellChain (q : ℕ) :
    NormalizedCubicalChain (MooreLoopSpace X b) k q →ₗ[k]
      NormalizedCubicalChain (MoorePathPullback f b) k (q + (m + 1)) :=
  NormalizedCubicalChain.map k (cellMap τ h₀ h₁) (q + (m + 1)) ∘ₗ
    (NormalizedCubicalChain.crossProduct _ _ k q (m + 1)).flip
      (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))

theorem cellChain_apply {q : ℕ} (c : NormalizedCubicalChain (MooreLoopSpace X b) k q) :
    cellChain τ h₀ h₁ k q c =
      NormalizedCubicalChain.map k (cellMap τ h₀ h₁) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct _ _ k q (m + 1) c
          (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) :=
  (rfl)

/-- On a cube `c`, the cell chain map is the cube `F ∘ (c × [Iᵐ⁺¹])`. -/
@[simp]
theorem cellChain_ofCube {q : ℕ} (c : SingularCube (MooreLoopSpace X b) q) :
    cellChain τ h₀ h₁ k q (NormalizedCubicalChain.ofCube _ k c) =
      NormalizedCubicalChain.ofCube _ k
        ((cellMap τ h₀ h₁).comp (SingularCube.crossProduct c (upCube.{0} (m + 1)))) := by
  simp [cellChain_apply, NormalizedCubicalChain.map_ofCube]

/-- **The cell chain map is linear over the loop chains**:
`a · F_*(c × [Iᵐ⁺¹]) = F_*(a c × [Iᵐ⁺¹])` for the Pontryagin product `a c` and the left action of
`C_*(Ω_b X)` on the chains of the pulled-back path fibration, after the reindexing
`(p + q) + (m + 1) = p + (q + (m + 1))`. -/
theorem leftAct_cellChain {p q : ℕ} (a : NormalizedCubicalChain (MooreLoopSpace X b) k p)
    (c : NormalizedCubicalChain (MooreLoopSpace X b) k q) :
    NormalizedCubicalChain.leftAct _ _ k p (q + (m + 1)) a (cellChain τ h₀ h₁ k q c) =
      NormalizedCubicalChain.cast k (Nat.add_assoc p q (m + 1))
        (cellChain τ h₀ h₁ k (p + q) (NormalizedCubicalChain.mul _ k p q a c)) := by
  rw [NormalizedCubicalChain.leftAct_def, cellChain_apply, cellChain_apply,
    NormalizedCubicalChain.mul_def]
  refine (NormalizedCubicalChain.map_crossProduct_map_assoc k ?_ a c _).symm
  ext x : 1
  simpa [Homeomorph.prodAssoc, Equiv.prodAssoc] using cellMap_mul τ h₀ h₁ x.1.1 x.1.2 x.2

/-- The generator `c_f = F_*([1] × [Iᵐ⁺¹])` of the chains over the cell, the image of the
fundamental cube under `v ↦ F (1, v)` (`TauCeti.MoorePathPullback.cellGenerator_eq_ofCube`). -/
def cellGenerator : NormalizedCubicalChain (MoorePathPullback f b) k (0 + (m + 1)) :=
  cellChain τ h₀ h₁ k 0 (NormalizedCubicalChain.one _ k)

/-- The generator is the cube `v ↦ F (1, v)`: the cross product of the `0`-cube at the unit loop
with the identity cube, pushed forward along the cell map. -/
theorem cellGenerator_eq_ofCube :
    cellGenerator τ h₀ h₁ k = NormalizedCubicalChain.ofCube _ k ((cellMap τ h₀ h₁).comp
      (SingularCube.crossProduct (SingularCube.point (1 : MooreLoopSpace X b))
        (upCube.{0} (m + 1)))) := by
  rw [cellGenerator, NormalizedCubicalChain.one_def, cellChain_ofCube]

/-- **The loop chains act on the generator through the cell map**: `a · c_f = F_*(a × [Iᵐ⁺¹])`,
after the reindexing `p + (m + 1) = p + (0 + (m + 1))`. -/
theorem leftAct_cellGenerator {p : ℕ} (a : NormalizedCubicalChain (MooreLoopSpace X b) k p) :
    NormalizedCubicalChain.leftAct _ _ k p (0 + (m + 1)) a (cellGenerator τ h₀ h₁ k) =
      NormalizedCubicalChain.cast k (Nat.add_assoc p 0 (m + 1)) (cellChain τ h₀ h₁ k p a) := by
  rw [cellGenerator, leftAct_cellChain, NormalizedCubicalChain.mul_one_eq_self]
  rfl

/-! ### The relative homology over the cell -/

/-- **The relative homology of the based path fibration over a cubical cell**: taking the cross
product with the fundamental cycle `[Iᵐ⁺¹]` and pushing forward along the cell map is an isomorphism
`H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f*P_b X, f*P_b X|_{∂Iᵐ⁺¹}; k)`, over every commutative ring `k`
(`TauCeti.MoorePathPullback.cellHomologyEquiv_homologyπ`). -/
def cellHomologyEquiv (q : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homology q ≃ₗ[k]
      ((cellPair f b).cubicalChainComplex k).homology (q + (m + 1)) :=
  cubicalHomologyCubeBoundaryPairProdLeftEquiv k (TopCat.of (MooreLoopSpace X b)) m q ≪≫ₗ
    (homologyMapIso (TopPair.cubicalChainComplexIso k (cubeBoundaryPairProdLeftIso (m + 1)
      (TopCat.of (MooreLoopSpace X b)))) (q + (m + 1))).toLinearEquiv ≪≫ₗ
    (((fiberHomotopyEquiv τ h₀ h₁).relativeCubicalChainHomotopyEquiv
      (ULift.down ⁻¹' Cube.boundary (Fin (m + 1))) k).toHomologyIso (q + (m + 1))).toLinearEquiv

/-- The ambient map of the comparison of `Ω_b X × (Iᵐ⁺¹, ∂Iᵐ⁺¹)` with the pulled-back pair is the
cell map. -/
private theorem fst_cubeBoundaryPairProdLeftIso_hom_comp_preimagePairMap :
    TopPair.Hom.fst ((cubeBoundaryPairProdLeftIso (m + 1) (TopCat.of (MooreLoopSpace X b))).hom ≫
        (fiberHomotopyEquiv τ h₀ h₁).preimagePairMap
          (ULift.down ⁻¹' Cube.boundary (Fin (m + 1)))) =
      TopCat.ofHom (cellMap τ h₀ h₁) := by
  rw [TopPair.Hom.fst_comp, cubeBoundaryPairProdLeftIso_hom_fst,
    FiberHomotopyEquiv.preimagePairMap_fst, fiberHomotopyEquiv_toFun, cellMap, TopCat.ofHom_comp]
  -- The two composites differ only in the `TopCat` object presenting `Ω_b X × Iᵐ⁺¹`: the monoidal
  -- product of the factors, or `TopCat.of` of their product.
  rfl

/-- On chains, the comparison of `Ω_b X × (Iᵐ⁺¹, ∂Iᵐ⁺¹)` with the pulled-back pair is the
push-forward along the cell map, followed by the projection to relative chains. -/
private theorem cubicalChainComplexMap_f_π (n : ℕ)
    (y : ((normalizedCubicalChainComplex k).obj
      ((cubeBoundaryPair.{0} (m + 1)).prodLeft (TopCat.of (MooreLoopSpace X b))).fst).X n) :
    (TopPair.cubicalChainComplexMap k ((cubeBoundaryPairProdLeftIso (m + 1)
        (TopCat.of (MooreLoopSpace X b))).hom ≫ (fiberHomotopyEquiv τ h₀ h₁).preimagePairMap
          (ULift.down ⁻¹' Cube.boundary (Fin (m + 1))))).f n
      ((Limits.cokernel.π ((normalizedCubicalChainComplex k).map
        ((cubeBoundaryPair.{0} (m + 1)).prodLeft (TopCat.of (MooreLoopSpace X b))).map)).f n y) =
    (Limits.cokernel.π ((normalizedCubicalChainComplex k).map (cellPair f b).map)).f n
      (((normalizedCubicalChainComplex k).map (TopCat.ofHom (cellMap τ h₀ h₁))).f n y) := by
  rw [← fst_cubeBoundaryPairProdLeftIso_hom_comp_preimagePairMap, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, TopPair.π_cubicalChainComplexMap, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply]
  -- The two sides differ only in how the embedding of the target pair is written: as
  -- `(cellPair f b).map` or through the codomain of the composite map of pairs.
  rfl

/-- **The isomorphism on cycles.** `TauCeti.MoorePathPullback.cellHomologyEquiv` sends the class of
a cycle `z` of `Ω_b X` to the class of any relative cycle `w` whose underlying chain is the class of
`F_*(z × [Iᵐ⁺¹])` (`TauCeti.MoorePathPullback.cellChain`). -/
theorem cellHomologyEquiv_homologyπ {q : ℕ}
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).cycles q)
    (w : ((cellPair f b).cubicalChainComplex k).cycles (q + (m + 1)))
    (hw : ((cellPair f b).cubicalChainComplex k).iCycles (q + (m + 1)) w =
      (Limits.cokernel.π ((normalizedCubicalChainComplex k).map (cellPair f b).map)).f
        (q + (m + 1)) ((normalizedCubicalChainComplexXEquiv _ _).symm (cellChain τ h₀ h₁ k q
          (normalizedCubicalChainComplexXEquiv _ q
            (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).iCycles q
              z))))) :
    cellHomologyEquiv τ h₀ h₁ k q
        (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homologyπ q z) =
      ((cellPair f b).cubicalChainComplex k).homologyπ (q + (m + 1)) w := by
  -- Each of the three isomorphisms is induced by a chain map, so the class of `z` goes to the class
  -- of the image of the cycle `z ⊗ [Iᵐ⁺¹]` under their composite; compare underlying chains.
  simp only [cellHomologyEquiv, LinearEquiv.trans_apply,
    cubicalHomologyCubeBoundaryPairProdLeftEquiv_homologyπ, Iso.toLinearEquiv_apply,
    homologyMapIso_hom]
  -- `HomotopyEquiv.toHomologyIso` has no simp lemma for its forward map.
  rw [show ∀ i, (_root_.HomotopyEquiv.toHomologyIso
      ((fiberHomotopyEquiv τ h₀ h₁).relativeCubicalChainHomotopyEquiv
        (ULift.down ⁻¹' Cube.boundary (Fin (m + 1))) k) i).hom =
      homologyMap ((fiberHomotopyEquiv τ h₀ h₁).relativeCubicalChainHomotopyEquiv
        (ULift.down ⁻¹' Cube.boundary (Fin (m + 1))) k).hom i from fun _ ↦ rfl]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, homologyπ_naturality_assoc,
    homologyπ_naturality]
  simp only [ModuleCat.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles _ _)).1 inferInstance
  rw [hw]
  have hi {K L : ChainComplex (ModuleCat.{0} k) ℕ} (φ : K ⟶ L) (n : ℕ) (x : K.cycles n) :
      L.iCycles n (cyclesMap φ n x) = φ.f n (K.iCycles n x) :=
    ConcreteCategory.congr_hom (cyclesMap_i φ n) x
  rw [hi, hi, hi]
  -- The underlying chain of `z ⊗ [Iᵐ⁺¹]` is the tensor product of `z` and the identity cube.
  have hx := ConcreteCategory.congr_hom (cyclesCross_iCycles
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b)))
    ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex k) q (m + 1) (q + (m + 1)) rfl)
    (z ⊗ₜ cubeBoundaryPairCycle k m)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    iCycles_cubeBoundaryPairCycle] at hx
  -- `erw`: the chains of `normalizedCubicalChainComplex` and `NormalizedCubicalChain` are the same
  -- module only up to `normalizedCubicalChainComplexXEquiv`, which is the identity.
  erw [hx, TopPair.cubicalChainOfCube_def, cubicalCrossProductRel_f_ιTensorObj_tmul]
  rw [FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv_hom, TopPair.cubicalChainComplexIso_hom,
    ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← TopPair.cubicalChainComplexMap_comp]
  erw [cubicalChainComplexMap_f_π, NormalizedCubicalChain.cast_rfl]
  -- What remains is `cellChain_apply`, read through the identity
  -- `normalizedCubicalChainComplexXEquiv` and `normalizedCubicalChainComplex_map_f_apply`, both of
  -- which hold by `rfl`.
  rfl

end TauCeti.MoorePathPullback
