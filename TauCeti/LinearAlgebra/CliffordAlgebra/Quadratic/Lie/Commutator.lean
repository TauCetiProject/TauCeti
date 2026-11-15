/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Algebra.Lie.Isotypic
public import TauCeti.Algebra.Lie.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Representation
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Casimir
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# The commutator action on the Clifford algebra of the Killing form

Let `L` be a Killing-semisimple Lie algebra and `q = CliffordAlgebra.adjointCliffordHom K L` the
quadratic lift of its adjoint representation to the Clifford algebra of the Killing quadratic form.
The lift makes the Clifford algebra an `L`-module in two ways. Kostant's module
(`CliffordAlgebra.kostantLieModule`) lets `L` act by left multiplication, `⁅x, c⁆ = q x * c`, and
is isotypic (`CliffordAlgebra.kostant_isotypic`). This file studies the other one, the action by
inner derivations of `CliffordAlgebra.cliffordDerivationRep`,

`⁅x, c⁆ = ⁅q x, c⁆ = q x * c - c * q x`,

which under `CliffordAlgebra.equivExterior` is the exterior extension of the adjoint
representation. Its submodules include three that are visible directly in the Clifford algebra:
the centre, on which `L` acts trivially; the Clifford generators `ι L`, a copy of the adjoint
module; and the quadratic elements `q L`, a second copy of the adjoint module. Because the adjoint
module of a Killing-semisimple Lie algebra has no nonzero invariant vector, the trivial and the
adjoint pieces share no irreducible constituent, and the commutator module is **not** isotypic as
soon as `L` is nonzero.

In dimension three, the four pieces `K • 1`, `ι L`, `q L` and the odd part of the centre already
exhaust the eight-dimensional Clifford algebra, so the commutator module is
`1 ⊕ L ⊕ L ⊕ 1`. For `L = 𝔰𝔩₂` this is the decomposition `⋀𝔰𝔩₂ ≅ 1 ⊕ V(2) ⊕ V(2) ⊕ 1`, to be set
against Kostant's left-regular decomposition of the same eight-dimensional space into four copies
of one two-dimensional irreducible module.

## Main definitions

* `CliffordAlgebra.Commutator.instLieRingModule` and `CliffordAlgebra.Commutator.instLieModule`:
  the commutator action, as scoped instances; write
  `open scoped CliffordAlgebra.Commutator` to use them. They are scoped apart from Kostant's
  instances in `CliffordAlgebra`, because both act on the same carrier.

## Main results

* `CliffordAlgebra.commutator_lie_def`: the defining equation of the commutator action.
* `CliffordAlgebra.commutator_toEnd`: the action is `CliffordAlgebra.cliffordDerivationRep` of
  the Killing adjoint action.
* `CliffordAlgebra.commutator_lie_ι` and `CliffordAlgebra.commutator_lie_adjointCliffordHom`: the
  generators and the quadratic elements carry the adjoint action.
* `CliffordAlgebra.commutator_lie_eq_zero_of_mem_center`: central elements are invariant.
* `CliffordAlgebra.ι_mem_maxTrivSubmodule_commutator_iff`: no nonzero generator is invariant.
* `CliffordAlgebra.not_isIsotypic_commutator`: for nonzero `L`, the commutator module is not
  isotypic.
* `CliffordAlgebra.exists_lieModuleEquiv_commutator_of_finrank_eq_three`: in dimension three,
  the commutator module is `1 ⊕ L ⊕ L ⊕ 1`.
* `CliffordAlgebra.nonempty_lieModuleEquiv_commutator_sl_fin_two`: the commutator module of `𝔰𝔩₂`
  is `1 ⊕ V(2) ⊕ V(2) ⊕ 1`; contrast `CliffordAlgebra.kostant_multiplicity_sl_fin_two`.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem, the ρ-decomposition
  `C(𝔤) = End V_ρ ⊗ C(P)`, and the `𝔤`-module structure of `⋀𝔤`*, Adv. Math. 125 (1997), 275--350.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013), Chapter 7.
-/

public section

universe u v

open TauCeti TauCeti.LieAlgebra LieModule Module

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L]

namespace Commutator

/-- **The commutator module.** The Clifford algebra of the Killing quadratic form, acted on by `L`
through the inner derivations `c ↦ ⁅q x, c⁆` of the adjoint quadratic lift `q`, that is, through
`CliffordAlgebra.cliffordDerivationRep`. Scoped: Kostant's left-regular action
`CliffordAlgebra.kostantLieRingModule` is a competing `L`-module structure on the same carrier. -/
noncomputable scoped instance instLieRingModule :
    LieRingModule L (CliffordAlgebra (killingQuadraticForm K L)) :=
  LieRingModule.compLieHom _ (cliffordDerivationRep (killingQuadraticForm K L)
    (killingQuadraticForm_nondegenerate K L) (killingAdjointSO K L))

/-- The commutator module is a Lie module over the base field. -/
noncomputable scoped instance instLieModule :
    LieModule K L (CliffordAlgebra (killingQuadraticForm K L)) :=
  LieModule.compLieHom _ _

end Commutator

section Commutator

open scoped CliffordAlgebra.Commutator

/-- **The commutator module is the representation `CliffordAlgebra.cliffordDerivationRep`** of the
Killing adjoint action. -/
theorem commutator_toEnd :
    toEnd K L (CliffordAlgebra (killingQuadraticForm K L)) =
      cliffordDerivationRep (killingQuadraticForm K L) (killingQuadraticForm_nondegenerate K L)
        (killingAdjointSO K L) := by
  ext x c
  rw [toEnd_apply_apply]
  exact LieRingModule.compLieHom_apply _ _ _ _

variable {K L}

/-- **The defining equation of the commutator module**: `L` acts by the commutator with the
adjoint quadratic lift. -/
@[simp, grind =]
theorem commutator_lie_def (x : L) (c : CliffordAlgebra (killingQuadraticForm K L)) :
    ⁅x, c⁆ = ⁅adjointCliffordHom K L x, c⁆ := by
  rw [← toEnd_apply_apply (R := K), commutator_toEnd, cliffordDerivationRep_apply,
    adjointCliffordHom_apply]

/-- **The generators carry the adjoint action.** Unlike in Kostant's module
(`CliffordAlgebra.kostant_lie_ι`), there is no right-multiplication term. -/
@[grind =]
theorem commutator_lie_ι (x y : L) :
    ⁅x, ι (killingQuadraticForm K L) y⁆ = ι (killingQuadraticForm K L) ⁅x, y⁆ := by
  rw [commutator_lie_def, adjointCliffordHom_lie_ι]

/-- **The quadratic elements carry the adjoint action**, because the quadratic lift is a Lie
algebra homomorphism. -/
@[grind =]
theorem commutator_lie_adjointCliffordHom (x y : L) :
    ⁅x, adjointCliffordHom K L y⁆ = adjointCliffordHom K L ⁅x, y⁆ := by
  rw [commutator_lie_def, LieHom.map_lie]

/-- **Central elements are invariant** under the commutator action. -/
theorem commutator_lie_eq_zero_of_mem_center {c : CliffordAlgebra (killingQuadraticForm K L)}
    (hc : c ∈ Subalgebra.center K (CliffordAlgebra (killingQuadraticForm K L))) (x : L) :
    ⁅x, c⁆ = 0 := by
  rw [commutator_lie_def, LieRing.of_associative_ring_bracket,
    Subalgebra.mem_center_iff.mp hc, sub_self]

/-- **No nonzero generator is invariant** under the commutator action: an invariant generator
`ι y` has `⁅x, y⁆ = 0` for all `x`, and the centre of a Killing-semisimple Lie algebra vanishes. -/
theorem ι_mem_maxTrivSubmodule_commutator_iff (y : L) :
    ι (killingQuadraticForm K L) y ∈
        maxTrivSubmodule K L (CliffordAlgebra (killingQuadraticForm K L)) ↔ y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hy : y ∈ _root_.LieAlgebra.center K L := by
    rw [_root_.LieAlgebra.center, mem_maxTrivSubmodule]
    intro x
    rw [← ι_eq_zero_iff (killingQuadraticForm K L), ← commutator_lie_ι]
    exact (mem_maxTrivSubmodule K L _ _).mp h x
  rwa [_root_.LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at hy

/-- The Clifford generators, as a Lie submodule of the commutator module. -/
private noncomputable def generatorSubmodule :
    LieSubmodule K L (CliffordAlgebra (killingQuadraticForm K L)) :=
  { LinearMap.range (ι (killingQuadraticForm K L)) with
    lie_mem := by
      rintro x _ ⟨y, rfl⟩
      exact ⟨⁅x, y⁆, (commutator_lie_ι x y).symm⟩ }

/-- **The commutator module is not isotypic.** For a nonzero Killing-semisimple Lie algebra `L`,
the commutator action on the Clifford algebra of the Killing form has two irreducible submodules
that are not isomorphic: one on which `L` acts trivially, which exists because the scalars are
invariant, and one inside the Clifford generators, which carry the adjoint action. Compare
`CliffordAlgebra.kostant_isotypic` for the left-regular action on the same carrier. -/
theorem not_isIsotypic_commutator [Nontrivial L] :
    ¬ IsIsotypic K L (CliffordAlgebra (killingQuadraticForm K L)) := by
  intro h
  -- An irreducible submodule on which `L` acts trivially; the scalars show that one exists.
  have hT : maxTrivSubmodule K L (CliffordAlgebra (killingQuadraticForm K L)) ≠ ⊥ := by
    rw [ne_eq, LieSubmodule.eq_bot_iff]
    exact fun hbot ↦ one_ne_zero (hbot 1 fun x ↦ by
      simpa using commutator_lie_eq_zero_of_mem_center (Subalgebra.center K _).one_mem x)
  obtain ⟨T, hTatom, hTle⟩ := (eq_bot_or_exists_atom_le _).resolve_left hT
  -- An irreducible submodule of the generators.
  have hG : (generatorSubmodule : LieSubmodule K L (CliffordAlgebra (killingQuadraticForm K L)))
      ≠ ⊥ := by
    obtain ⟨y, hy⟩ := exists_ne (0 : L)
    rw [ne_eq, LieSubmodule.eq_bot_iff]
    exact fun hbot ↦ hy <| (ι_eq_zero_iff (killingQuadraticForm K L) y).mp (hbot _ ⟨y, rfl⟩)
  obtain ⟨G, hGatom, hGle⟩ := (eq_bot_or_exists_atom_le _).resolve_left hG
  have := (isIrreducible_iff_isAtom T).mpr hTatom
  have := (isIrreducible_iff_isAtom G).mpr hGatom
  -- Isotypy would make `G` trivial, but no nonzero generator is invariant.
  obtain ⟨e⟩ := (isIsotypicOfType_iff K L _ _).mp ((isIsotypic_iff K L _).mp h T) G
  refine hGatom.1 ((LieSubmodule.eq_bot_iff _).mpr fun c hc ↦ ?_)
  obtain ⟨y, rfl⟩ := hGle hc
  have hinv : ι (killingQuadraticForm K L) y ∈
      maxTrivSubmodule K L (CliffordAlgebra (killingQuadraticForm K L)) := by
    refine (mem_maxTrivSubmodule K L _ _).mpr fun x ↦ ?_
    have hx : ⁅x, e ⟨_, hc⟩⁆ = 0 :=
      Subtype.ext ((mem_maxTrivSubmodule K L _ _).mp (hTle (e ⟨_, hc⟩).2) x)
    have hmap : e ⁅x, ⟨_, hc⟩⁆ = ⁅x, e ⟨_, hc⟩⁆ := e.map_lie'
    rw [← hmap, EmbeddingLike.map_eq_zero_iff] at hx
    exact congrArg Subtype.val hx
  rw [(ι_mem_maxTrivSubmodule_commutator_iff y).mp hinv, map_zero]

/-- The four pieces of the commutator module in dimension three, assembled along a central
element `ω`: `(a, y, z, b) ↦ a + ι y + q z + b • ω`. -/
private noncomputable def decompositionHom (ω : CliffordAlgebra (killingQuadraticForm K L))
    (hω : ω ∈ Subalgebra.center K (CliffordAlgebra (killingQuadraticForm K L))) :
    TrivialLieModule K L K × L × L × TrivialLieModule K L K →ₗ⁅K,L⁆
      CliffordAlgebra (killingQuadraticForm K L) where
  toFun p := algebraMap K _ (TrivialLieModule.equiv K L K p.1) +
    ι (killingQuadraticForm K L) p.2.1 + adjointCliffordHom K L p.2.2.1 +
      TrivialLieModule.equiv K L K p.2.2.2 • ω
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, Algebra.algebraMap_eq_smul_one,
      RingHom.id_apply, smul_add, mul_smul]
  map_lie' {x p} := by
    simp only [lie_prod_apply, trivial_lie_zero, map_zero, zero_smul, zero_add, add_zero, lie_add,
      commutator_lie_ι, commutator_lie_adjointCliffordHom,
      commutator_lie_eq_zero_of_mem_center (Subalgebra.algebraMap_mem _ _),
      commutator_lie_eq_zero_of_mem_center (Subalgebra.smul_mem _ hω _)]

private theorem decompositionHom_apply (ω : CliffordAlgebra (killingQuadraticForm K L))
    (hω : ω ∈ Subalgebra.center K (CliffordAlgebra (killingQuadraticForm K L)))
    (p : TrivialLieModule K L K × L × L × TrivialLieModule K L K) :
    decompositionHom ω hω p = algebraMap K _ (TrivialLieModule.equiv K L K p.1) +
      ι (killingQuadraticForm K L) p.2.1 + adjointCliffordHom K L p.2.2.1 +
        TrivialLieModule.equiv K L K p.2.2.2 • ω :=
  (rfl)

/-- Along a nonzero odd central element `ω`, the assembly map is injective: the even part
`a + q z` and the odd part `ι y + b • ω` of its value vanish separately, the scalar part of the
first is `a`, and `ω` is not a generator. -/
private theorem decompositionHom_injective {ω : CliffordAlgebra (killingQuadraticForm K L)}
    (hωc : ω ∈ Subalgebra.center K (CliffordAlgebra (killingQuadraticForm K L)))
    (hωo : ω ∈ evenOdd (killingQuadraticForm K L) 1) (hω : ω ≠ 0) :
    Function.Injective (decompositionHom ω hωc) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, y, z, b⟩ hp
  set a' := TrivialLieModule.equiv K L K a with ha'
  set b' := TrivialLieModule.equiv K L K b with hb'
  have hsum : (algebraMap K _ a' + adjointCliffordHom K L z) +
      (ι (killingQuadraticForm K L) y + b' • ω) = 0 := by
    rw [← hp, decompositionHom_apply, ← ha', ← hb']
    abel
  -- Split into even and odd parts.
  have he :
      algebraMap K _ a' + adjointCliffordHom K L z ∈ evenOdd (killingQuadraticForm K L) 0 := by
    refine add_mem ?_ ?_
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.one_le.mp (one_le_evenOdd_zero _))
    · rw [adjointCliffordHom_apply]
      exact quadraticLieSubalgebra_le_evenOdd_zero _
        ((LieSubalgebra.mem_toSubmodule _).mpr (soEquivQuadratic _ _ _).property)
  have ho : ι (killingQuadraticForm K L) y + b' • ω ∈ evenOdd (killingQuadraticForm K L) 1 :=
    add_mem (ι_mem_evenOdd_one _ _) (Submodule.smul_mem _ _ hωo)
  have he0 := Submodule.disjoint_def.mp (evenOdd_isCompl _).disjoint _ he
    (by rw [eq_neg_of_add_eq_zero_left hsum]; exact neg_mem ho)
  have ho0 : ι (killingQuadraticForm K L) y + b' • ω = 0 := by rwa [he0, zero_add] at hsum
  -- The scalar part of the even part is `a`.
  have ha : a' = 0 := by
    have htr := congrArg (scalarTrace (killingQuadraticForm K L)) he0
    rwa [map_add, scalarTrace_algebraMap, scalarTrace_adjointCliffordHom, add_zero,
      map_zero] at htr
  have hz : z = 0 := by
    rw [ha, map_zero, zero_add] at he0
    exact (adjointCliffordHom_injective K L).eq_iff' (map_zero _) |>.mp he0
  -- A nonzero odd part would make `ω` a generator, but no nonzero generator is central.
  have hb : b' = 0 := by
    by_contra hb
    have hωι : ω = ι (killingQuadraticForm K L) (-b'⁻¹ • y) := by
      rw [map_smul, eq_neg_of_add_eq_zero_left ho0, smul_neg, neg_smul, neg_neg, smul_smul,
        inv_mul_cancel₀ hb, one_smul]
    refine hω (hωι.trans ?_)
    rw [(ι_mem_maxTrivSubmodule_commutator_iff (-b'⁻¹ • y)).mp
      ((mem_maxTrivSubmodule K L _ _).mpr fun x ↦ hωι ▸ commutator_lie_eq_zero_of_mem_center hωc x),
      map_zero]
  have hy : y = 0 := by
    rwa [hb, zero_smul, add_zero, ι_eq_zero_iff] at ho0
  simp only [Prod.mk_eq_zero, hy, hz, true_and]
  exact ⟨(TrivialLieModule.equiv K L K).map_eq_zero_iff.mp ha,
    (TrivialLieModule.equiv K L K).map_eq_zero_iff.mp hb⟩

/-- **The commutator module in dimension three is `1 ⊕ L ⊕ L ⊕ 1`.** For a three-dimensional
Killing-semisimple Lie algebra `L`, there is an odd central element `ω` of the Clifford algebra of
the Killing form such that `(a, y, z, b) ↦ a + ι y + q z + b • ω` is an equivalence of Lie modules
from `1 ⊕ L ⊕ L ⊕ 1` (trivial lines and adjoint modules) onto the commutator module. So the
summands are the scalars, the Clifford generators, the quadratic elements and the line `K • ω`.
For `L = 𝔰𝔩₂` this is `⋀𝔰𝔩₂ ≅ 1 ⊕ V(2) ⊕ V(2) ⊕ 1`; the module is not isotypic,
`CliffordAlgebra.not_isIsotypic_commutator`. -/
theorem exists_lieModuleEquiv_commutator_of_finrank_eq_three (h : finrank K L = 3) :
    ∃ ω ∈ Subalgebra.center K (CliffordAlgebra (killingQuadraticForm K L)),
      ω ∈ evenOdd (killingQuadraticForm K L) 1 ∧
      ∃ e : LieModuleEquiv K L (TrivialLieModule K L K × L × L × TrivialLieModule K L K)
          (CliffordAlgebra (killingQuadraticForm K L)),
        ∀ p, e p = algebraMap K _ (TrivialLieModule.equiv K L K p.1) +
          ι (killingQuadraticForm K L) p.2.1 + adjointCliffordHom K L p.2.2.1 +
            TrivialLieModule.equiv K L K p.2.2.2 • ω := by
  -- The volume element of an orthogonal basis is an odd central element.
  obtain ⟨l, hl, hlen, hspan, hQl⟩ :=
    (killingQuadraticForm_nondegenerate K L).exists_list_pairwise_isOrtho
  have hodd : Odd l.length := by rw [hlen, h]; decide
  have hω : (l.map (ι (killingQuadraticForm K L))).prod ≠ 0 :=
    (isUnit_prod_map_ι
      (List.prod_ne_zero (by simpa using fun v hv h ↦ hQl v hv h)).isUnit).ne_zero
  have hωc := prod_map_ι_mem_center_of_odd_length hl hodd hspan
  have hωo := prod_map_ι_mem_evenOdd_one_of_odd_length (Q := killingQuadraticForm K L) hodd
  have hinj := decompositionHom_injective hωc hωo hω
  -- Both sides have dimension eight.
  have _ : Module.Finite K (TrivialLieModule K L K) :=
    Module.Finite.equiv (TrivialLieModule.equiv K L K).symm
  have hdim : finrank K (TrivialLieModule K L K × L × L × TrivialLieModule K L K) =
      finrank K (CliffordAlgebra (killingQuadraticForm K L)) := by
    rw [finrank_eq_two_pow, h, finrank_prod, finrank_prod, finrank_prod,
      (TrivialLieModule.equiv K L K).finrank_eq, h, finrank_self]
    norm_num
  have hbij : Function.Bijective (decompositionHom _ hωc) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  exact ⟨_, hωc, hωo, LieModuleEquiv.ofBijective _ hbij,
    fun p ↦ (LieModuleEquiv.ofBijective_apply _ hbij p).trans (decompositionHom_apply _ hωc p)⟩

open _root_.LieAlgebra.SpecialLinear in
/-- **The commutator action of `𝔰𝔩₂`**: `⋀𝔰𝔩₂ ≅ 1 ⊕ V(2) ⊕ V(2) ⊕ 1`, with `V(2)` the
three-dimensional adjoint module. -/
theorem nonempty_lieModuleEquiv_commutator_sl_fin_two [CharZero K] :
    Nonempty (CliffordAlgebra (killingQuadraticForm K (sl (Fin 2) K)) ≃ₗ⁅K,sl (Fin 2) K⁆
      TrivialLieModule K (sl (Fin 2) K) K × sl (Fin 2) K × sl (Fin 2) K ×
        TrivialLieModule K (sl (Fin 2) K) K) :=
  have ⟨_, _, _, e, _⟩ := exists_lieModuleEquiv_commutator_of_finrank_eq_three
    (K := K) (L := sl (Fin 2) K) (by simp [finrank_sl])
  ⟨e.symm⟩

end Commutator

end CliffordAlgebra
