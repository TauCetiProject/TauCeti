/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Lattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.DirectSum
import TauCeti.Algebra.Lie.HighestWeight.Irreducible

/-!
# Diagram symmetries of the fundamental modules and of the full-weight module

Let `σ` be a symmetry of the Bourbaki-numbered Cartan matrix of a valid Dynkin type `t`, and
`TauCeti.DynkinType.diagramLieEquiv` the automorphism `hᵢ ↦ h_{σ i}`, `eᵢ ↦ e_{σ i}`,
`fᵢ ↦ f_{σ i}` of the pinned rational Lie algebra. Twisting the fundamental module `L(ϖ_{σ i})` by
this automorphism gives an irreducible module in which `v⁺_{σ i}` is a highest weight vector of
weight `ϖᵢ`, since `ϖ_{σ i}(h_{σ j}) = ϖᵢ(hⱼ)`. By the classification of irreducible highest
weight modules it is therefore `L(ϖᵢ)`. The result is a linear equivalence

```text
θ_{σ,i} : L(ϖᵢ) ≃ L(ϖ_{σ i}),   θ_{σ,i} v⁺ᵢ = v⁺_{σ i},   θ_{σ,i} (x v) = σ(x) θ_{σ,i}(v),
```

and it is the only linear map with these two properties. It also matches the integral structures:
the enveloping-algebra map of the diagram automorphism permutes the generators of the
simple-generator Kostant form `U_ℤ`, so `θ_{σ,i}` maps the fundamental lattice `U_ℤ v⁺ᵢ` of
`L(ϖᵢ)` onto the fundamental lattice `U_ℤ v⁺_{σ i}` of `L(ϖ_{σ i})`.

Assembling these over the summands gives the automorphism `θ_σ` of the full-weight module
`V_sc(t) = ⨁ᵢ L(ϖᵢ)` that carries the `i`-th summand to the `σ i`-th one. It intertwines the
action of `x` with that of `σ(x)`, in particular the action of `e_{±αᵢ}` with that of
`e_{±α_{σ i}}`, which is the intertwining hypothesis of the numbered symmetries of Kostant data in
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.NumberedSymmetry`. Uniqueness
makes `σ ↦ θ_σ` a homomorphism from the diagram symmetry group: `θ_1 = 1` and
`θ_{στ} = θ_σ ∘ θ_τ`. The direct sum of all fundamental modules is stable under every diagram
symmetry, so one module carries all of them.

## Main definitions

* `TauCeti.DynkinType.fundamentalModuleDiagramEquiv`: the equivalence `L(ϖᵢ) ≃ L(ϖ_{σ i})`.
* `TauCeti.DynkinType.scModuleDiagramEquiv`: the automorphism `θ_σ` of `V_sc(t)`.

## Main results

* `TauCeti.DynkinType.fundamentalModuleDiagramEquiv_fundamentalModuleGenerator` and
  `TauCeti.DynkinType.fundamentalModuleDiagramEquiv_lie`: `v⁺ᵢ ↦ v⁺_{σ i}`, and the action of `x`
  becomes the action of the diagram automorphism applied to `x`;
  `TauCeti.DynkinType.eq_fundamentalModuleDiagramEquiv`: these characterize it.
* `TauCeti.DynkinType.fundamentalModuleDiagramEquiv_mem_fundamentalLattice_iff`: `θ_{σ,i}` maps
  the fundamental lattice of `L(ϖᵢ)` onto that of `L(ϖ_{σ i})`.
* `TauCeti.DynkinType.scModuleDiagramEquiv_lof` and `TauCeti.DynkinType.scModuleDiagramEquiv_lie`:
  `θ_σ` maps the `i`-th summand to the `σ i`-th one by `θ_{σ,i}`, and intertwines the action of
  `x` with that of its image under the diagram automorphism;
  `TauCeti.DynkinType.eq_scModuleDiagramEquiv`: these characterize it.
* `TauCeti.DynkinType.scModuleDiagramEquiv_one`, `TauCeti.DynkinType.scModuleDiagramEquiv_mul`
  and `TauCeti.DynkinType.scModuleDiagramEquiv_symm`: `σ ↦ θ_σ` is a homomorphism.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2, Corollary 1 to Theorem 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §20.3 and
  §27.1.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieModule Module DirectSum

noncomputable section

-- Endomorphism algebras are Lie rings through their commutator; the enveloping-algebra
-- representations below are Lie homomorphisms into them, as in
-- `TauCeti/Algebra/Lie/UniversalEnveloping/Basic.lean`.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} (ht : t.Valid) {σ τ : Equiv.Perm (Fin t.rank)}

/-! ### The fundamental modules -/

/-- Renumbering the Cartan generators by `σ` turns `ϖ_{σ i}` into `ϖᵢ`. -/
private theorem fundamentalWeight_cartanBasis_equiv (i : Fin t.rank)
    (x : t.cartanSubalgebra ht) :
    t.fundamentalWeight ht (σ i) ((t.cartanBasis ht).equiv (t.cartanBasis ht) σ x) =
      t.fundamentalWeight ht i x := by
  have h : (t.fundamentalWeight ht (σ i)).comp
      ((t.cartanBasis ht).equiv (t.cartanBasis ht) σ).toLinearMap = t.fundamentalWeight ht i :=
    (t.cartanBasis ht).ext fun k => by
      have hb (j : Fin t.rank) : t.cartanBasis ht j = (t.lieBasis ht).h' j :=
        Subtype.ext (t.coe_cartanBasis ht j)
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply, hb, hb,
        fundamentalWeight_apply_h', fundamentalWeight_apply_h']
      simp only [σ.injective.eq_iff]
  exact congr($h x)

/-- Through the diagram automorphism, the Cartan subalgebra acts on `v⁺_{σ i}` by `ϖᵢ`. -/
private theorem lie_diagramLieEquiv_fundamentalModuleGenerator (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) (x : t.cartanSubalgebra ht) :
    ⁅t.diagramLieEquiv ht hσ x, t.fundamentalModuleGenerator ht (σ i)⁆ =
      t.fundamentalWeight ht i x • t.fundamentalModuleGenerator ht (σ i) := by
  rw [diagramLieEquiv_cartan,
    (t.isHighestWeightVector_fundamentalModuleGenerator ht (σ i)).lie_eq_smul,
    fundamentalWeight_cartanBasis_equiv]

/-- Through the diagram automorphism, the positive nilradical annihilates `v⁺_{σ i}`: it is
generated by the raising generators, which the automorphism permutes. -/
private theorem lie_diagramLieEquiv_fundamentalModuleGenerator_of_mem
    (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) {x : t.lieAlgebra ht}
    (hx : x ∈ positiveNilradical (t.cartanSubalgebra ht) (t.lieBasis ht).base) :
    ⁅t.diagramLieEquiv ht hσ x, t.fundamentalModuleGenerator ht (σ i)⁆ = 0 := by
  rw [(t.lieBasis ht).positiveNilradical_eq_lieSpan_e] at hx
  have hle : LieSubalgebra.lieSpan ℚ (t.lieAlgebra ht) (Set.range (t.lieBasis ht).e) ≤
      (lieAnnihilator ℚ (t.lieAlgebra ht) (t.fundamentalModuleGenerator ht (σ i))).comap
        (t.diagramLieEquiv ht hσ).toLieHom :=
    LieSubalgebra.lieSpan_le.mpr <| by
      rintro _ ⟨j, rfl⟩
      simp
  simpa using hle hx

/-- **The diagram symmetry of the fundamental modules**: the linear equivalence
`θ_{σ,i} : L(ϖᵢ) ≃ L(ϖ_{σ i})` carrying `v⁺ᵢ` to `v⁺_{σ i}` and the action of each `x` to the
action of its image under the diagram automorphism `TauCeti.DynkinType.diagramLieEquiv`. -/
def fundamentalModuleDiagramEquiv (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) :
    t.fundamentalModule ht i ≃ₗ[ℚ] t.fundamentalModule ht (σ i) :=
  twistedEquivOfIsHighestWeightVector (t.diagramLieEquiv ht hσ).toLieHom
    (t.diagramLieEquiv ht hσ).surjective (t.isHighestWeightVector_fundamentalModuleGenerator ht i)
    (t.fundamentalModuleGenerator_ne_zero ht (σ i))
    (lie_diagramLieEquiv_fundamentalModuleGenerator ht hσ i)
    fun _ hx => lie_diagramLieEquiv_fundamentalModuleGenerator_of_mem ht hσ i hx

/-- `θ_{σ,i}` carries the highest weight vector `v⁺ᵢ` to `v⁺_{σ i}`. -/
@[simp]
theorem fundamentalModuleDiagramEquiv_fundamentalModuleGenerator (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) :
    t.fundamentalModuleDiagramEquiv ht hσ i (t.fundamentalModuleGenerator ht i) =
      t.fundamentalModuleGenerator ht (σ i) :=
  twistedEquivOfIsHighestWeightVector_apply_self _ _ _ _ _

/-- **`θ_{σ,i}` intertwines the action of `x` with that of its image under the diagram
automorphism.** -/
theorem fundamentalModuleDiagramEquiv_lie (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank)
    (x : t.lieAlgebra ht) (m : t.fundamentalModule ht i) :
    t.fundamentalModuleDiagramEquiv ht hσ i ⁅x, m⁆ =
      ⁅t.diagramLieEquiv ht hσ x, t.fundamentalModuleDiagramEquiv ht hσ i m⁆ :=
  twistedEquivOfIsHighestWeightVector_lie _ _ _ _ _ x m

/-- **`θ_{σ,i}` is characterized by its two defining properties**: a linear map
`L(ϖᵢ) → L(ϖ_{σ i})` carrying `v⁺ᵢ` to `v⁺_{σ i}` and the action of each `x` to the action of its
image under the diagram automorphism is `θ_{σ,i}`. -/
theorem eq_fundamentalModuleDiagramEquiv (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank)
    {f : t.fundamentalModule ht i →ₗ[ℚ] t.fundamentalModule ht (σ i)}
    (hf : ∀ x m, f ⁅x, m⁆ = ⁅t.diagramLieEquiv ht hσ x, f m⁆)
    (hfv : f (t.fundamentalModuleGenerator ht i) = t.fundamentalModuleGenerator ht (σ i)) :
    f = t.fundamentalModuleDiagramEquiv ht hσ i :=
  eq_twistedEquivOfIsHighestWeightVector _ _ _ _ _ hf hfv

/-! ### The fundamental lattices -/

/-- The enveloping-algebra map of a diagram automorphism maps the Kostant form into itself, since
the automorphism permutes the raising, lowering and Cartan generators. -/
private theorem map_diagramLieEquiv_kostantForm_le (hσ : σ ∈ t.diagramSymmetry) :
    (t.kostantForm ht).map
        (UniversalEnvelopingAlgebra.map ℚ (t.diagramLieEquiv ht hσ).toLieHom).toRingHom ≤
      t.kostantForm ht := by
  rw [kostantForm_def, LieAlgebra.Basis.kostantForm_def, UniversalEnvelopingAlgebra.map_kostantForm,
    UniversalEnvelopingAlgebra.kostantForm_le_iff, ← LieAlgebra.Basis.kostantForm_def]
  refine ⟨fun i n => ?_, fun i n => ?_⟩
  · rcases i with j | j
    · simpa using (t.lieBasis ht).dividedPower_mem_kostantForm (.inl (σ j)) n
    · simpa using (t.lieBasis ht).dividedPower_mem_kostantForm (.inr (σ j)) n
  · simpa using (t.lieBasis ht).ringChoose_mem_kostantForm (σ i) n

/-- `θ_{σ,i}` intertwines the action of `u ∈ U(L)` with that of its image under the
enveloping-algebra map of the diagram automorphism. -/
private theorem fundamentalModuleDiagramEquiv_representation (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) (u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht))
    (m : t.fundamentalModule ht i) :
    t.fundamentalModuleDiagramEquiv ht hσ i
        (UniversalEnvelopingAlgebra.representation ℚ _ _ u m) =
      UniversalEnvelopingAlgebra.representation ℚ _ _
        (UniversalEnvelopingAlgebra.map ℚ (t.diagramLieEquiv ht hσ).toLieHom u)
        (t.fundamentalModuleDiagramEquiv ht hσ i m) := by
  -- Both sides, conjugated back to `L(ϖᵢ)`, are algebra maps `U(L) → End L(ϖᵢ)` agreeing on `L`.
  have h : ((t.fundamentalModuleDiagramEquiv ht hσ i).conjAlgEquiv ℚ).toAlgHom.comp
        (UniversalEnvelopingAlgebra.representation ℚ (t.lieAlgebra ht)
          (t.fundamentalModule ht i)) =
      (UniversalEnvelopingAlgebra.representation ℚ (t.lieAlgebra ht)
        (t.fundamentalModule ht (σ i))).comp
        (UniversalEnvelopingAlgebra.map ℚ (t.diagramLieEquiv ht hσ).toLieHom) := by
    apply _root_.UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => LinearMap.ext fun n => ?_
    simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
      UniversalEnvelopingAlgebra.map_ι, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
      LinearMap.comp_apply,
      UniversalEnvelopingAlgebra.representation_ι_apply, LinearEquiv.coe_coe,
      fundamentalModuleDiagramEquiv_lie, LinearEquiv.apply_symm_apply, LieEquiv.coe_toLieHom]
  have hu := congr($h u (t.fundamentalModuleDiagramEquiv ht hσ i m))
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hu
  exact hu

/-- `θ_{σ,i}` carries the fundamental lattice of `L(ϖᵢ)` into that of `L(ϖ_{σ i})`. -/
private theorem fundamentalModuleDiagramEquiv_mem_fundamentalLattice (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) {m : t.fundamentalModule ht i} (hm : m ∈ t.fundamentalLattice ht i) :
    t.fundamentalModuleDiagramEquiv ht hσ i m ∈ t.fundamentalLattice ht (σ i) := by
  have hle : t.fundamentalLattice ht i ≤ (t.fundamentalLattice ht (σ i)).comap
      ((t.fundamentalModuleDiagramEquiv ht hσ i).toLinearMap.restrictScalars ℤ) := by
    rw [t.fundamentalLattice_def ht i, Subring.orbitOfRep_le_iff]
    rintro u hu _ rfl
    simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      fundamentalModuleDiagramEquiv_representation,
      fundamentalModuleDiagramEquiv_fundamentalModuleGenerator]
    exact t.representation_mem_fundamentalLattice ht
      (map_diagramLieEquiv_kostantForm_le ht hσ ⟨u, hu, rfl⟩)
      (t.fundamentalModuleGenerator_mem_fundamentalLattice ht (σ i))
  exact hle hm

/-- **`θ_{σ,i}` matches the fundamental lattices**: it carries a vector of `L(ϖᵢ)` into the
fundamental lattice of `L(ϖ_{σ i})` exactly when the vector lies in the fundamental lattice of
`L(ϖᵢ)`. -/
@[simp]
theorem fundamentalModuleDiagramEquiv_mem_fundamentalLattice_iff (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) {m : t.fundamentalModule ht i} :
    t.fundamentalModuleDiagramEquiv ht hσ i m ∈ t.fundamentalLattice ht (σ i) ↔
      m ∈ t.fundamentalLattice ht i := by
  refine ⟨fun hm => ?_, fundamentalModuleDiagramEquiv_mem_fundamentalLattice ht hσ i⟩
  -- Every vector `u v⁺_{σ i}` of the target lattice is `θ_{σ,i} (u' v⁺ᵢ)`, with `u'` the image of
  -- `u` under the enveloping-algebra map of the inverse automorphism, again in the Kostant form.
  suffices hle : t.fundamentalLattice ht (σ i) ≤ (t.fundamentalLattice ht i).map
      ((t.fundamentalModuleDiagramEquiv ht hσ i).toLinearMap.restrictScalars ℤ) by
    obtain ⟨m', hm', hθ⟩ := hle hm
    rwa [← (t.fundamentalModuleDiagramEquiv ht hσ i).injective hθ]
  rw [t.fundamentalLattice_def ht (σ i), Subring.orbitOfRep_le_iff]
  rintro u hu _ rfl
  have hu' : UniversalEnvelopingAlgebra.map ℚ (t.diagramLieEquiv ht hσ).symm.toLieHom u ∈
      t.kostantForm ht := by
    rw [diagramLieEquiv_symm]
    exact map_diagramLieEquiv_kostantForm_le ht _ ⟨u, hu, rfl⟩
  have hΘ : UniversalEnvelopingAlgebra.map ℚ (t.diagramLieEquiv ht hσ).toLieHom
      (UniversalEnvelopingAlgebra.map ℚ (t.diagramLieEquiv ht hσ).symm.toLieHom u) = u := by
    have hcomp :
        (t.diagramLieEquiv ht hσ).toLieHom.comp (t.diagramLieEquiv ht hσ).symm.toLieHom =
          LieHom.id :=
      LieHom.ext (t.diagramLieEquiv ht hσ).apply_symm_apply
    rw [← AlgHom.comp_apply, ← UniversalEnvelopingAlgebra.map_comp, hcomp,
      UniversalEnvelopingAlgebra.map_id, AlgHom.id_apply]
  refine ⟨_, t.representation_mem_fundamentalLattice ht hu'
    (t.fundamentalModuleGenerator_mem_fundamentalLattice ht i), ?_⟩
  simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    fundamentalModuleDiagramEquiv_representation,
    fundamentalModuleDiagramEquiv_fundamentalModuleGenerator, hΘ]

/-! ### The full-weight module -/

/-- **A linear endomorphism of `V_sc(t)` intertwining the action of `x` with that of `φ x` is
determined by the images of the highest weight vectors `v⁺ᵢ` of the summands**, which generate
`V_sc(t)`. -/
private theorem scModule_linearMap_ext (φ : t.lieAlgebra ht → t.lieAlgebra ht)
    {f g : t.scModule ht →ₗ[ℚ] t.scModule ht} (hf : ∀ x v, f ⁅x, v⁆ = ⁅φ x, f v⁆)
    (hg : ∀ x v, g ⁅x, v⁆ = ⁅φ x, g v⁆)
    (h : ∀ i, f (lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i)) =
      g (lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i))) :
    f = g :=
  DirectSum.linearMap_ext ℚ fun i =>
    LinearMap.ext_on_of_lieSpan_eq_top (lieSpan_irreducibleQuotientGenerator_eq_top _ _) φ
      (fun x m => by simp only [LinearMap.comp_apply, lof_lie ℚ, hf])
      (fun x m => by simp only [LinearMap.comp_apply, lof_lie ℚ, hg])
      (Set.eqOn_singleton.mpr (h i))

/-- The underlying linear map of `θ_σ`: the sum over `i` of `θ_{σ,i}` followed by the inclusion
of the `σ i`-th summand. -/
private def scModuleDiagramMap (hσ : σ ∈ t.diagramSymmetry) :
    t.scModule ht →ₗ[ℚ] t.scModule ht :=
  toModule ℚ _ _ fun i =>
    lof ℚ _ (t.fundamentalModule ht) (σ i) ∘ₗ (t.fundamentalModuleDiagramEquiv ht hσ i).toLinearMap

private theorem scModuleDiagramMap_lof (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank)
    (m : t.fundamentalModule ht i) :
    scModuleDiagramMap ht hσ (lof ℚ _ (t.fundamentalModule ht) i m) =
      lof ℚ _ (t.fundamentalModule ht) (σ i) (t.fundamentalModuleDiagramEquiv ht hσ i m) := by
  simp [scModuleDiagramMap]

private theorem scModuleDiagramMap_lie (hσ : σ ∈ t.diagramSymmetry) (x : t.lieAlgebra ht)
    (v : t.scModule ht) :
    scModuleDiagramMap ht hσ ⁅x, v⁆ = ⁅t.diagramLieEquiv ht hσ x, scModuleDiagramMap ht hσ v⁆ := by
  have h : scModuleDiagramMap ht hσ ∘ₗ toEnd ℚ _ _ x =
      toEnd ℚ _ _ (t.diagramLieEquiv ht hσ x) ∘ₗ scModuleDiagramMap ht hσ :=
    DirectSum.linearMap_ext ℚ fun i => LinearMap.ext fun m => by
      simp only [LinearMap.comp_apply, toEnd_apply_apply, ← lof_lie ℚ, scModuleDiagramMap_lof,
        fundamentalModuleDiagramEquiv_lie]
  simpa using congr($h v)

private theorem scModuleDiagramMap_congr {hσ : σ ∈ t.diagramSymmetry}
    {hτ : τ ∈ t.diagramSymmetry} (h : σ = τ) :
    scModuleDiagramMap ht hσ = scModuleDiagramMap ht hτ := by
  subst h
  rfl

private theorem scModuleDiagramMap_one :
    scModuleDiagramMap ht t.diagramSymmetry.one_mem = LinearMap.id := by
  refine scModule_linearMap_ext ht id (fun x v => ?_)
    (fun x v => by rw [LinearMap.id_apply, LinearMap.id_apply, id]) fun i => ?_
  · simp only [scModuleDiagramMap_lie, diagramLieEquiv_one, LieEquiv.refl_apply, id_eq]
  · simp only [scModuleDiagramMap_lof, fundamentalModuleDiagramEquiv_fundamentalModuleGenerator,
      LinearMap.id_apply]
    -- `(1 : Equiv.Perm _) i` reduces to `i`, so the two summand indices agree by `rfl`.
    rfl

private theorem scModuleDiagramMap_mul (hσ : σ ∈ t.diagramSymmetry)
    (hτ : τ ∈ t.diagramSymmetry) :
    scModuleDiagramMap ht (t.diagramSymmetry.mul_mem hσ hτ) =
      scModuleDiagramMap ht hσ ∘ₗ scModuleDiagramMap ht hτ := by
  refine scModule_linearMap_ext ht (t.diagramLieEquiv ht (t.diagramSymmetry.mul_mem hσ hτ))
    (scModuleDiagramMap_lie ht _) (fun x v => ?_) fun i => ?_
  · simp only [LinearMap.comp_apply, scModuleDiagramMap_lie]
    rw [diagramLieEquiv_mul ht hσ hτ]
    -- What is left is `LieEquiv.trans_apply`, which holds by `rfl`; rewriting with it instead
    -- makes `rw` unfold every other coercion in the goal while looking for its pattern.
    rfl
  · simp only [LinearMap.comp_apply, scModuleDiagramMap_lof,
      fundamentalModuleDiagramEquiv_fundamentalModuleGenerator]
    -- `(σ * τ) i` reduces to `σ (τ i)`, so the two summand indices agree by `rfl`.
    rfl

/-- **The diagram symmetry `θ_σ` of the full-weight module** `V_sc(t) = ⨁ᵢ L(ϖᵢ)`: the
automorphism mapping the `i`-th summand to the `σ i`-th one by
`TauCeti.DynkinType.fundamentalModuleDiagramEquiv`. It carries the action of each `x` to the
action of its image under the diagram automorphism `TauCeti.DynkinType.diagramLieEquiv`. -/
def scModuleDiagramEquiv (hσ : σ ∈ t.diagramSymmetry) : t.scModule ht ≃ₗ[ℚ] t.scModule ht :=
  LinearEquiv.ofLinearMap (scModuleDiagramMap ht hσ)
    (scModuleDiagramMap ht (t.diagramSymmetry.inv_mem hσ))
    (by rw [← scModuleDiagramMap_mul, ← scModuleDiagramMap_one ht]
        exact scModuleDiagramMap_congr ht (mul_inv_cancel σ))
    (by rw [← scModuleDiagramMap_mul, ← scModuleDiagramMap_one ht]
        exact scModuleDiagramMap_congr ht (inv_mul_cancel σ))

/-- **`θ_σ` maps the `i`-th summand to the `σ i`-th one** by `θ_{σ,i}`. -/
@[simp]
theorem scModuleDiagramEquiv_lof (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank)
    (m : t.fundamentalModule ht i) :
    t.scModuleDiagramEquiv ht hσ (lof ℚ _ (t.fundamentalModule ht) i m) =
      lof ℚ _ (t.fundamentalModule ht) (σ i) (t.fundamentalModuleDiagramEquiv ht hσ i m) :=
  scModuleDiagramMap_lof ht hσ i m

/-- **`θ_σ` intertwines the action of `x` with that of its image under the diagram
automorphism.** In particular it carries the action of `eᵢ`, `fᵢ` and `hᵢ` to that of `e_{σ i}`,
`f_{σ i}` and `h_{σ i}`. -/
theorem scModuleDiagramEquiv_lie (hσ : σ ∈ t.diagramSymmetry) (x : t.lieAlgebra ht)
    (v : t.scModule ht) :
    t.scModuleDiagramEquiv ht hσ ⁅x, v⁆ =
      ⁅t.diagramLieEquiv ht hσ x, t.scModuleDiagramEquiv ht hσ v⁆ :=
  scModuleDiagramMap_lie ht hσ x v

/-- **`θ_σ` is characterized by its defining properties**: a linear endomorphism of `V_sc(t)`
carrying the action of each `x` to the action of its image under the diagram automorphism, and
each highest weight vector `v⁺ᵢ` of the `i`-th summand to `v⁺_{σ i}` in the `σ i`-th summand, is
`θ_σ`. -/
theorem eq_scModuleDiagramEquiv (hσ : σ ∈ t.diagramSymmetry)
    {f : t.scModule ht →ₗ[ℚ] t.scModule ht}
    (hf : ∀ x v, f ⁅x, v⁆ = ⁅t.diagramLieEquiv ht hσ x, f v⁆)
    (hfv : ∀ i, f (lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i)) =
      lof ℚ _ (t.fundamentalModule ht) (σ i) (t.fundamentalModuleGenerator ht (σ i))) :
    f = t.scModuleDiagramEquiv ht hσ :=
  scModule_linearMap_ext ht (t.diagramLieEquiv ht hσ) hf (scModuleDiagramEquiv_lie ht hσ)
    fun i => by simp [hfv]

/-- The identity symmetry of the diagram gives the identity of `V_sc(t)`. -/
@[simp]
theorem scModuleDiagramEquiv_one :
    t.scModuleDiagramEquiv ht t.diagramSymmetry.one_mem = LinearEquiv.refl ℚ _ :=
  LinearEquiv.toLinearMap_injective (scModuleDiagramMap_one ht)

/-- **`θ_{στ} = θ_σ ∘ θ_τ`**, the right-hand symmetry acting first. -/
theorem scModuleDiagramEquiv_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry) :
    t.scModuleDiagramEquiv ht (t.diagramSymmetry.mul_mem hσ hτ) =
      (t.scModuleDiagramEquiv ht hτ).trans (t.scModuleDiagramEquiv ht hσ) :=
  LinearEquiv.toLinearMap_injective (scModuleDiagramMap_mul ht hσ hτ)

/-- The inverse of `θ_σ` is `θ_{σ⁻¹}`. -/
@[simp]
theorem scModuleDiagramEquiv_symm (hσ : σ ∈ t.diagramSymmetry) :
    (t.scModuleDiagramEquiv ht hσ).symm =
      t.scModuleDiagramEquiv ht (t.diagramSymmetry.inv_mem hσ) := by
  -- Both sides are built from the maps of `σ⁻¹` and of `σ⁻¹⁻¹`, which is `σ` by `rfl`.
  rw [scModuleDiagramEquiv, scModuleDiagramEquiv, LinearEquiv.symm_ofLinearMap]

end

end TauCeti.DynkinType
