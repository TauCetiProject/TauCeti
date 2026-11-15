/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Subgroup

/-!
# Graph automorphisms of the simply connected Chevalley group

For a symmetry `σ` of the Bourbaki-numbered Dynkin diagram of `t`, the **graph automorphism**
`γ_σ = TauCeti.DynkinType.chevalleyGraphAut ht hσ A` of the points `G_sc(t)(A)` of the simply
connected Chevalley group is conjugation by the matrix of the integral lattice symmetry
`TauCeti.DynkinType.scModuleDiagramEquiv` of the full-weight module. It is stated on
`TauCeti.DynkinType.chevalleyGroup` with the root subgroups, torus and Frobenius of the full-weight
Chevalley datum, so that it composes with the rest of the Chevalley-datum API.

Over every commutative ring `A`:

* `γ_σ (x_{±αᵢ}(u)) = x_{±α_{σ i}}(u)` on the positive and negative simple roots, and
  `γ_σ (x_α(u)) = x_{σ α}(ε_{σ,α} u)` on every root, with the sign
  `ε_{σ,α} = TauCeti.DynkinType.chevalleyDiagramSign ht hσ α` read from the structure constants;
* `γ_σ (T(s)) = T(s ∘ σ⁻¹)` on the torus in fundamental-weight coordinates, so the character
  pullback of `γ_σ` is the weight map of the inverse diagram automorphism of the simply connected
  root datum;
* `γ_σ γ_τ = γ_{στ}`, `γ_1 = 1`, and every order relation of `σ` holds for `γ_σ`;
* `γ_σ` commutes with the point maps induced by ring homomorphisms, in particular with every
  Frobenius map.

None of these statements uses generation of the points by root subgroups. Composed with a
Frobenius map, `γ_σ` gives the Steinberg endomorphisms of the ordinary and graph-twisted finite
groups of Lie type.

## Main definitions

* `TauCeti.DynkinType.chevalleyGraphAut`: the graph automorphism of `G_sc(t)(A)`.

## Main results

* `TauCeti.DynkinType.chevalleyGraphAut_rootSubgroupPoints`: the signed action on every root
  subgroup.
* `TauCeti.DynkinType.chevalleyGraphAut_rootSubgroupPoints_simpleIndex` and
  `TauCeti.DynkinType.chevalleyGraphAut_rootSubgroupPoints_reflectionPerm_simpleIndex`: the pinned
  action on the positive and negative simple root subgroups.
* `TauCeti.DynkinType.isCharacterMap_chevalleyGraphAut`: the character pullback.
* `TauCeti.DynkinType.chevalleyGraphAut_mul` and
  `TauCeti.DynkinType.chevalleyGraphAut_pow_eq_one`: composition and order relations.
* `TauCeti.DynkinType.comp_chevalleyGraphAut` and
  `TauCeti.DynkinType.chevalleyGraphAut_comp_frobenius`: naturality in the value ring, and
  commutation with Frobenius.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  §§1.15–1.17.
-/

public section

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v v'

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {σ τ : Equiv.Perm (Fin t.rank)}

/-- **The graph automorphism** `γ_σ` of the points of the simply connected Chevalley group
attached to a symmetry `σ` of the numbered Dynkin diagram: conjugation by the matrix of the
integral lattice symmetry of the full-weight module realizing `σ`. -/
def chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    MulAut (t.chevalleyGroup ht A) :=
  kostantNumberedSymmetryPoints (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
    (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
    A (t.chevalleyGroup ht A) (by
      rw [chevalleyGroup_eq_kostantToralPointsSubgroup]
      exact map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) (diagramRootGeneratorPerm σ)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        (t.scModuleDiagramEquiv_representation_rootGenerator ht hσ)
        (diagramRootGeneratorPerm σ).surjective σ
        (fun _ _ hxy => t.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero ht hσ hxy) A)

/-- On matrices, the graph automorphism is conjugation by the lattice symmetry matrix. -/
@[simp]
theorem coe_chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    (g : t.chevalleyGroup ht A) :
    (t.chevalleyGraphAut ht hσ A g :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A * g *
      (kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A)⁻¹ :=
  coe_kostantNumberedSymmetryPoints _ _ _ _ A _ _ g

/-- On matrices, the inverse graph automorphism is conjugation by the inverse lattice symmetry
matrix. -/
@[simp]
theorem coe_chevalleyGraphAut_symm (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    (g : t.chevalleyGroup ht A) :
    ((t.chevalleyGraphAut ht hσ A).symm g :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      (kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A)⁻¹ * g *
      kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A :=
  coe_kostantNumberedSymmetryPoints_symm _ _ _ _ A _ _ g

/-! ### Root subgroups -/

/-- **The graph automorphism on every root subgroup.** It sends `x_α(u)` to `x_{σ α}(ε u)`, where
`σ α` is the image of `α` under the diagram symmetry and `ε = ±1` is the sign by which the
diagram automorphism of the Lie algebra carries the Chevalley root vector at `α` to the one at
`σ α`. -/
@[simp]
theorem chevalleyGraphAut_rootSubgroupPoints (hσ : σ ∈ t.diagramSymmetry) (α : Fin t.numRoots)
    (A : Type v) [CommRing A] (u : A) :
    t.chevalleyGraphAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints α A (Multiplicative.ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.diagramRootPerm ht hσ α) A
        (Multiplicative.ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u)) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (t.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints ht hσ α A u)
  refine (t.coe_chevalleyGraphAut ht hσ A _).trans ?_
  refine (congrArg
    (fun x : Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A => _ * x * _)
    (((t.scChevalleyDatum ht).coe_rootSubgroupPoints α A _).trans
      (coe_chevalleyToralRootSubgroupPoints _ _ _ _ _ (t.scWeight ht) α A _).symm)).trans ?_
  refine ((coe_scToralDiagramAutPoints ht hσ A _).symm.trans h).trans ?_
  exact (coe_chevalleyToralRootSubgroupPoints _ _ _ _ _ _ _ A _).trans
    ((t.scChevalleyDatum ht).coe_rootSubgroupPoints _ A _).symm

/-- **The graph automorphism on a positive simple root subgroup**:
`γ_σ (x_{αᵢ}(u)) = x_{α_{σ i}}(u)`. -/
@[simp]
theorem chevalleyGraphAut_rootSubgroupPoints_simpleIndex (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    t.chevalleyGraphAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht i) A u) =
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht (σ i)) A u := by
  simpa using t.chevalleyGraphAut_rootSubgroupPoints ht hσ (t.simpleIndex ht i) A
    (Multiplicative.toAdd u)

/-- **The graph automorphism on a negative simple root subgroup**:
`γ_σ (x_{-αᵢ}(u)) = x_{-α_{σ i}}(u)`. -/
@[simp]
theorem chevalleyGraphAut_rootSubgroupPoints_reflectionPerm_simpleIndex
    (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    t.chevalleyGraphAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
            (t.simpleIndex ht i)) A u) =
      (t.scChevalleyDatum ht).rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht (σ i))
          (t.simpleIndex ht (σ i))) A u := by
  have hp := (t.diagramAut ht hσ).toHom.indexEquiv_reflectionPerm (t.simpleIndex ht i)
    (t.simpleIndex ht i)
  simp only [diagramAut_indexEquiv, diagramRootPerm_simpleIndex] at hp
  simpa [hp] using t.chevalleyGraphAut_rootSubgroupPoints ht hσ
    ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i))
    A (Multiplicative.toAdd u)

/-! ### The torus and the character map -/

/-- **The character map of the graph automorphism.** `γ_σ` pulls characters of the torus back by
the weight map of the inverse diagram automorphism of the simply connected root datum, which
precomposes a character, in fundamental-weight coordinates, with `σ`. -/
theorem isCharacterMap_chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry) (A : Type v)
    [CommRing A] :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A)
      (t.chevalleyGraphAut ht hσ A).toMonoidHom (diagramAut ht hσ)⁻¹.toHom.weightMap :=
  isCharacterMap_scChevalleyDatum_of_rootSubgroupPoints _ σ 1 1 (fun _ => pow_one _)
    (fun i u => by
      simp only [Pi.one_apply, Units.val_one, one_mul, pow_one]
      exact t.chevalleyGraphAut_rootSubgroupPoints_simpleIndex ht hσ i A _)
    (fun i u => by
      simp only [Pi.one_apply, inv_one, Units.val_one, one_mul, pow_one]
      exact t.chevalleyGraphAut_rootSubgroupPoints_reflectionPerm_simpleIndex ht hσ i A _)
    _ (fun χ i => by simp)

/-- **The graph automorphism on the torus** relabels the fundamental-weight coordinates by the
inverse symmetry: `γ_σ (T(s)) = T(s ∘ σ⁻¹)`. -/
@[simp]
theorem chevalleyGraphAut_torusPoints (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    (s : Fin t.rank → Aˣ) :
    t.chevalleyGraphAut ht hσ A ((t.scChevalleyDatum ht).torusPoints A s) =
      (t.scChevalleyDatum ht).torusPoints A (fun j => s (σ⁻¹ j)) := by
  refine ((t.isCharacterMap_chevalleyGraphAut ht hσ A).map_apply s).trans ?_
  apply congrArg ((t.scChevalleyDatum ht).torusPoints A)
  funext j
  have hsingle : LinearMap.funLeft ℤ ℤ σ (Pi.single j 1) =
      (Pi.single (σ.symm j) 1 : Fin t.rank → ℤ) :=
    Pi.single_comp_equiv σ j 1
  simp only [torusPointMap_apply, diagramAut_inv_weightMap, LinearEquiv.coe_coe,
    LinearEquiv.funCongrLeft_apply, hsingle, torusCharacter_single, zpow_one,
    Equiv.Perm.inv_def]

/-! ### Composition and order -/

/-- The graph automorphism has the matrices of the diagram action on the full-weight toral
closure, whose points are those of `G_sc(t)`. -/
private theorem coe_chevalleyGraphAut_eq (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    (g : t.chevalleyGroup ht A) :
    (t.chevalleyGraphAut ht hσ A g :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      t.scToralDiagramAutPoints ht hσ A
        ⟨g, (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A).le g.2⟩ := by
  rw [coe_scToralDiagramAutPoints]
  exact t.coe_chevalleyGraphAut ht hσ A g

/-- The identity diagram symmetry acts trivially. -/
@[simp]
theorem chevalleyGraphAut_one (A : Type v) [CommRing A] :
    t.chevalleyGraphAut ht t.diagramSymmetry.one_mem A = 1 :=
  MulEquiv.ext fun g => Subtype.ext <| (t.coe_chevalleyGraphAut_eq ht _ A g).trans <|
    congrArg Subtype.val (DFunLike.congr_fun (t.scToralDiagramAutPoints_one ht A) _)

/-- **Composition of diagram symmetries is composition of graph automorphisms**:
`γ_{στ} = γ_σ γ_τ`. -/
@[simp]
theorem chevalleyGraphAut_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    t.chevalleyGraphAut ht (t.diagramSymmetry.mul_mem hσ hτ) A =
      t.chevalleyGraphAut ht hσ A * t.chevalleyGraphAut ht hτ A :=
  MulEquiv.ext fun g => Subtype.ext <| (t.coe_chevalleyGraphAut_eq ht _ A g).trans <|
    (congrArg Subtype.val (DFunLike.congr_fun (t.scToralDiagramAutPoints_mul ht hσ hτ A) _)).trans
      ((t.coe_chevalleyGraphAut_eq ht hσ A _).trans
        (congrArg (fun x => (t.scToralDiagramAutPoints ht hσ A x :
          Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A))
          (Subtype.ext (t.coe_chevalleyGraphAut_eq ht hτ A g)))).symm

/-- **The diagram symmetry group acts on the points of `G_sc(t)`** through its graph
automorphisms. -/
def chevalleyGraphAutHom (A : Type v) [CommRing A] :
    t.diagramSymmetry →* MulAut (t.chevalleyGroup ht A) where
  toFun g := t.chevalleyGraphAut ht g.property A
  map_one' := t.chevalleyGraphAut_one ht A
  map_mul' g h := t.chevalleyGraphAut_mul ht g.property h.property A

/-- Evaluation of the bundled action is the graph automorphism. -/
@[simp]
theorem chevalleyGraphAutHom_apply (A : Type v) [CommRing A] (g : t.diagramSymmetry) :
    t.chevalleyGraphAutHom ht A g = t.chevalleyGraphAut ht g.property A :=
  (rfl)

/-- Inverting a diagram symmetry inverts its graph automorphism. -/
@[simp]
theorem chevalleyGraphAut_inv (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    t.chevalleyGraphAut ht (t.diagramSymmetry.inv_mem hσ) A =
      (t.chevalleyGraphAut ht hσ A)⁻¹ :=
  map_inv (t.chevalleyGraphAutHom ht A) ⟨σ, hσ⟩

/-- **Every order relation of a diagram symmetry holds for its graph automorphism.** In
particular the order of `γ_σ` divides the order of `σ`. -/
theorem chevalleyGraphAut_pow_eq_one (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    {m : ℕ} (hm : σ ^ m = 1) : t.chevalleyGraphAut ht hσ A ^ m = 1 :=
  (map_pow (t.chevalleyGraphAutHom ht A) ⟨σ, hσ⟩ m).symm.trans
    ((congrArg (t.chevalleyGraphAutHom ht A) (Subtype.ext hm :
      (⟨σ, hσ⟩ : t.diagramSymmetry) ^ m = 1)).trans (map_one _))

/-! ### Naturality in the value ring -/

/-- **The graph automorphism is natural in the value ring**: it commutes with the map of points
induced by any ring homomorphism. -/
theorem comp_chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry) {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (((t.scChevalleyDatum ht).pointsPresentation A).map
        ((t.scChevalleyDatum ht).pointsPresentation B) f).comp
      (t.chevalleyGraphAut ht hσ A).toMonoidHom =
    (t.chevalleyGraphAut ht hσ B).toMonoidHom.comp
      (((t.scChevalleyDatum ht).pointsPresentation A).map
        ((t.scChevalleyDatum ht).pointsPresentation B) f) :=
  comp_kostantNumberedSymmetryPoints _ _ _ _ _ _ _ _ f _
    (GeneralLinear.IntegralPointsPresentation.coe_map _ _ f)

/-- **The graph automorphism commutes with Frobenius.** -/
theorem chevalleyGraphAut_comp_frobenius (hσ : σ ∈ t.diagramSymmetry) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] :
    (t.chevalleyGraphAut ht hσ A).toMonoidHom.comp ((t.scChevalleyDatum ht).frobenius p k A) =
      ((t.scChevalleyDatum ht).frobenius p k A).comp (t.chevalleyGraphAut ht hσ A).toMonoidHom := by
  rw [ChevalleyDatum.frobenius_def]
  exact (t.comp_chevalleyGraphAut ht hσ (iterateFrobenius A p k)).symm

end

end TauCeti.DynkinType
