/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.GroupTheory.GroupAction.ConjAct
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Functoriality of the topological abelianization, and the conjugation action on `N^{ab}`

The topological abelianization `G^{ab} = G ⧸ closure [G, G]` of a topological group `G` is
Mathlib's `TopologicalAbelianization G`. This file adds two pieces of API to it.

**Functoriality.** A continuous homomorphism `f : G →* H` carries the topological closure of the
commutator subgroup of `G` into that of `H`, so it induces a continuous homomorphism
`TopologicalAbelianization.map f hf : G^{ab} →* H^{ab}`, compatible with identities and
composition.

**The conjugation action.** Let `N` be a normal subgroup of `G`. Conjugation by `G` preserves
`N`, hence its commutator subgroup, hence the topological closure of the latter, so it descends
to an action of `G` on `N^{ab}` by continuous group automorphisms; and an element of `N` acts on
`N^{ab}` trivially, because conjugation by it is an inner automorphism of `N`, so the action
factors through `G ⧸ N`. Both actions are recorded as `MulDistribMulAction` instances, the first
for Mathlib's conjugation type synonym `ConjAct G`, the second for the quotient `G ⧸ N`, and the
action of `G ⧸ N` is jointly continuous. On classes it is `(g : G ⧸ N) • (n : N^{ab}) = g n g⁻¹`,
the convention of `MulAut.conjNormal`.

This is the structure of Labute's relation module in the classification of Demushkin groups: for
a continuous character `χ` of a free pro-`p` group `F`, its kernel `X` is normal, and Labute's
`E = X ⧸ (X, X)` is `TopologicalAbelianization X` with `Γ = F ⧸ X` acting by conjugation
(Labute, §4, p. 121). Labute writes the action as `[y] · [x] = y⁻¹ x y`, which is the *inverse*
of the convention above: his `[y] · [x]` is `[y]⁻¹ • [x]` here (`mk_inv_smul_mk`). His formula
defines a left action when `Γ` is abelian, as it is in his setting (`Γ ≅ Im χ ≤ ℤ_pˣ`); for a
general normal subgroup it is a right action, which is why the instance uses Mathlib's convention
and Labute's action is recovered by precomposing with the inversion of the acting group.

## Main definitions

* `TopologicalAbelianization.map`: the homomorphism `G^{ab} →* H^{ab}` induced by a continuous
  homomorphism `G →* H`.
* The instances `MulDistribMulAction (ConjAct G) (TopologicalAbelianization N)` and
  `MulDistribMulAction (G ⧸ N) (TopologicalAbelianization N)`: conjugation on the topological
  abelianization of a normal subgroup, and its factorization through `G ⧸ N`.

## Main results

* `TopologicalAbelianization.map_mk`, `TopologicalAbelianization.continuous_map`,
  `TopologicalAbelianization.map_id`, `TopologicalAbelianization.map_comp`: the characteristic
  properties of `map`.
* `TopologicalAbelianization.mk_smul_mk`: the class of `g : G` acts on the class of `n : N` by
  the class of `g * n * g⁻¹`; `TopologicalAbelianization.mk_inv_smul_mk` is Labute's form of
  the same action, the inverse of the class of `g` acting by the class of `g⁻¹ * n * g`.
* `TopologicalAbelianization.toConjAct_smul_eq_self_of_mem`: elements of `N` act trivially on
  `N^{ab}`.
* The instances `ContinuousConstSMul (ConjAct G) (TopologicalAbelianization N)` and
  `ContinuousSMul (G ⧸ N) (TopologicalAbelianization N)`.
* `TopologicalAbelianization.map_inclusion_smul`,
  `TopologicalAbelianization.map_inclusion_quotient_smul`,
  `TopologicalAbelianization.map_inclusion_mk_smul`: for normal `R ≤ N`, the map
  `R^{ab} →* N^{ab}` induced by the inclusion is equivariant for conjugation by `G`, and
  intertwines the actions of `G ⧸ R` and `G ⧸ N` along the canonical map `G ⧸ R →* G ⧸ N`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4.
-/

public section

open scoped commutatorElement

namespace TopologicalAbelianization

section Map

variable {G H K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- A continuous homomorphism carries the topological closure of the commutator subgroup into
the topological closure of the commutator subgroup of the target. -/
theorem topologicalClosure_commutator_le_comap (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap f := by
  rw [← Subgroup.map_le_iff_le_comap]
  refine (f.map_topologicalClosure_le hf _).trans (Subgroup.topologicalClosure_mono ?_)
  rw [map_commutator_eq]
  exact Subgroup.commutator_mono le_top le_top

/-- The homomorphism `G^{ab} →* H^{ab}` between topological abelianizations induced by a
continuous homomorphism `f : G →* H`. -/
def map (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)

/-- `map f hf` sends the class of `x : G` to the class of `f x`. -/
@[simp]
theorem map_mk (f : G →* H) (hf : Continuous f) (x : G) :
    map f hf (x : TopologicalAbelianization G) = (f x : TopologicalAbelianization H) :=
  QuotientGroup.map_mk _ _ _ _ x

/-- The homomorphism `G^{ab} →* H^{ab}` induced by a continuous homomorphism is continuous. -/
theorem continuous_map (f : G →* H) (hf : Continuous f) : Continuous (map f hf) := by
  refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
  have h : map f hf ∘ (QuotientGroup.mk : G → TopologicalAbelianization G) =
      QuotientGroup.mk ∘ f := funext (map_mk f hf)
  rw [h]
  exact QuotientGroup.continuous_mk.comp hf

/-- The identity of `G` induces the identity of `G^{ab}`. -/
@[simp]
theorem map_id : map (MonoidHom.id G) continuous_id = MonoidHom.id (TopologicalAbelianization G) :=
  QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x => map_mk (MonoidHom.id G) continuous_id x)

/-- The topological abelianization is functorial: the map induced by a composite is the
composite of the induced maps. -/
theorem map_comp (g : H →* K) (hg : Continuous g) (f : G →* H) (hf : Continuous f) :
    (map g hg).comp (map f hf) = map (g.comp f) (hg.comp hf) :=
  QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x => by simp)

end Map

section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Conjugation by a fixed element of `G` is continuous on a normal subgroup. -/
instance [SeparatelyContinuousMul G] (N : Subgroup G) [N.Normal] :
    ContinuousConstSMul (ConjAct G) N where
  continuous_const_smul g :=
    continuous_induced_rng.2 ((continuous_const_smul g).comp continuous_subtype_val)

variable [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]

/-- The topological closure of the commutator subgroup of a normal subgroup `N` is stable under
conjugation by `G`. -/
theorem conjAct_smul_mem_topologicalClosure_commutator (g : ConjAct G) {n : N}
    (hn : n ∈ (commutator N).topologicalClosure) :
    g • n ∈ (commutator N).topologicalClosure := by
  have h := (MulDistribMulAction.toMonoidHom N g).map_topologicalClosure_le
    (continuous_const_smul g) (commutator N)
  refine (h.trans (Subgroup.topologicalClosure_mono ?_))
    (Subgroup.mem_map_of_mem (MulDistribMulAction.toMonoidHom N g) hn)
  rw [map_commutator_eq]
  exact Subgroup.commutator_mono le_top le_top

/-- Conjugation by `G` on a normal subgroup `N` descends to the topological abelianization of
`N`. -/
instance : MulAction.QuotientAction (ConjAct G) (commutator N).topologicalClosure where
  inv_mul_mem g _ _ h := by
    rw [← smul_inv', ← smul_mul']
    exact conjAct_smul_mem_topologicalClosure_commutator N g h

/-- **Conjugation on the topological abelianization of a normal subgroup.** The group `G`, as
`ConjAct G`, acts on `N^{ab}` by group automorphisms, with `g • (n : N^{ab}) = (g • n : N)`
(`MulAction.Quotient.smul_mk`). -/
instance instMulDistribMulActionConjAct :
    MulDistribMulAction (ConjAct G) (TopologicalAbelianization N) where
  toMulAction := inferInstance
  smul_mul g x y := by
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk,
      MulAction.Quotient.smul_mk, smul_mul', QuotientGroup.mk_mul]
  smul_one _ := by rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk, smul_one]

/-- Conjugation by `g : G` on `N^{ab}`, on the class of `n : N`: it is the class of the conjugate
`MulAut.conjNormal g n = g * n * g⁻¹`. -/
-- Not `@[simp]`: Mathlib's `@[simp] MulAction.Quotient.smul_mk` already rewrites the left-hand
-- side to `↑(ConjAct.toConjAct g • n)`, so simpNF rejects this lemma as a simp lemma.
theorem toConjAct_smul_mk (g : G) (n : N) :
    ConjAct.toConjAct g • (n : TopologicalAbelianization N) =
      (MulAut.conjNormal g n : TopologicalAbelianization N) :=
  MulAction.Quotient.smul_mk _ (ConjAct.toConjAct g) n

/-- Each conjugation is continuous on the topological abelianization of `N`. -/
instance : ContinuousConstSMul (ConjAct G) (TopologicalAbelianization N) where
  continuous_const_smul g := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    have h : (g • ·) ∘ (QuotientGroup.mk : N → TopologicalAbelianization N) =
        QuotientGroup.mk ∘ (g • ·) := funext (MulAction.Quotient.smul_mk _ g)
    rw [h]
    exact QuotientGroup.continuous_mk.comp (continuous_const_smul g)

/-- **Elements of `N` act trivially on `N^{ab}`**: conjugation by an element of `N` is an inner
automorphism of `N`, which is invisible in a commutative quotient. -/
theorem toConjAct_smul_eq_self_of_mem {g : G} (hg : g ∈ N) (x : TopologicalAbelianization N) :
    ConjAct.toConjAct g • x = x := by
  induction x using QuotientGroup.induction_on with | H x => ?_
  exact (QuotientGroup.mk' (commutator N).topologicalClosure).map_conjNormal_val ⟨g, hg⟩ x

/-- Conjugation by `G ⧸ N` on `N^{ab}`, as a homomorphism to the automorphism group: the
conjugation action of `G` factored through `G ⧸ N`. It is the homomorphism underlying the
`MulDistribMulAction (G ⧸ N) (TopologicalAbelianization N)` instance below (`conjAut_apply`),
whose defining equation is `mk_smul`. -/
def conjAut : G ⧸ N →* MulAut (TopologicalAbelianization N) :=
  QuotientGroup.lift N
    ((MulDistribMulAction.toMulAut (ConjAct G) (TopologicalAbelianization N)).comp
      ConjAct.toConjAct.toMonoidHom)
    fun _ hg => MonoidHom.mem_ker.2 (MulEquiv.ext (toConjAct_smul_eq_self_of_mem N hg))

/-- `conjAut N` sends the class of `g : G` to conjugation by `g` on `N^{ab}`, as an element of
`MulAut (TopologicalAbelianization N)`. -/
theorem conjAut_mk (g : G) :
    conjAut N (g : G ⧸ N) =
      MulDistribMulAction.toMulAut (ConjAct G) (TopologicalAbelianization N)
        (ConjAct.toConjAct g) :=
  QuotientGroup.lift_mk _ _ g

/-- **The conjugation action of `G ⧸ N` on the topological abelianization of `N`.** It is the
action of `G` by conjugation, which factors through `G ⧸ N` because `N` acts trivially
(`toConjAct_smul_eq_self_of_mem`); on classes, `(g : G ⧸ N) • (n : N^{ab}) = g * n * g⁻¹`
(`mk_smul_mk`). -/
instance instMulDistribMulActionQuotient :
    MulDistribMulAction (G ⧸ N) (TopologicalAbelianization N) where
  smul γ x := conjAut N γ x
  one_smul x := congrArg (fun e : MulAut (TopologicalAbelianization N) => e x) (map_one (conjAut N))
  mul_smul γ δ x :=
    congrArg (fun e : MulAut (TopologicalAbelianization N) => e x) (map_mul (conjAut N) γ δ)
  smul_mul _ _ _ := map_mul _ _ _
  smul_one _ := map_one _

/-- Applying the automorphism `conjAut N γ` is the action of `γ : G ⧸ N` on `N^{ab}`. -/
@[simp]
theorem conjAut_apply (γ : G ⧸ N) (x : TopologicalAbelianization N) : conjAut N γ x = γ • x :=
  rfl

/-- The class of `g : G` in `G ⧸ N` acts on `N^{ab}` as conjugation by `g`. -/
-- Not `@[simp]`: the class-level equations `mk_smul_mk` and `mk_inv_smul_mk` are the simp normal
-- form of the action; with this lemma in the simp set they would fail simpNF.
theorem mk_smul (g : G) (x : TopologicalAbelianization N) :
    (g : G ⧸ N) • x = ConjAct.toConjAct g • x := by
  rw [← conjAut_apply, conjAut_mk]
  -- `MulDistribMulAction.toMulAut` applies an element as the automorphism `x ↦ g • x`.
  rfl

/-- **The defining equation of the action of `G ⧸ N` on `N^{ab}`**: the class of `g` sends the
class of `n` to the class of `g * n * g⁻¹`. -/
@[simp]
theorem mk_smul_mk (g : G) (n : N) :
    (g : G ⧸ N) • (n : TopologicalAbelianization N) =
      (MulAut.conjNormal g n : TopologicalAbelianization N) := by
  rw [mk_smul, toConjAct_smul_mk]

/-- **Labute's form of the action** (§4 Definition, p. 121): the inverse of the class of `y`
sends the class of `x` to the class of `y⁻¹ * x * y`. Labute's `[y] · [x] = y⁻¹ x y` is thus
`(y : G ⧸ N)⁻¹ • [x]` in the convention of `mk_smul_mk`; the two agree up to the inversion of
the acting group, and Labute's formula is itself a left action when `G ⧸ N` is abelian. -/
@[simp]
theorem mk_inv_smul_mk (g : G) (n : N) :
    (g : G ⧸ N)⁻¹ • (n : TopologicalAbelianization N) =
      ((⟨g⁻¹ * n * g, ‹N.Normal›.conj_mem' n n.2 g⟩ : N) : TopologicalAbelianization N) := by
  rw [← QuotientGroup.mk_inv, mk_smul_mk]
  exact congrArg _ (Subtype.ext (by simp))

/-- The conjugation action of `G ⧸ N` on `N^{ab}` is jointly continuous. -/
instance : ContinuousSMul (G ⧸ N) (TopologicalAbelianization N) where
  continuous_smul := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap
      QuotientGroup.isOpenQuotientMap_mk).continuous_comp_iff]
    have h : (fun p : (G ⧸ N) × TopologicalAbelianization N => p.1 • p.2) ∘
        Prod.map QuotientGroup.mk QuotientGroup.mk =
          QuotientGroup.mk ∘ fun p : G × N => MulAut.conjNormal p.1 p.2 :=
      funext fun p => mk_smul_mk N p.1 p.2
    rw [h]
    refine QuotientGroup.continuous_mk.comp (continuous_induced_rng.2 ?_)
    simp only [Function.comp_def, MulAut.conjNormal_apply]
    exact IsTopologicalGroup.continuous_conj_prod.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

variable {R : Subgroup G} [R.Normal] {N}

/-- For normal subgroups `R ≤ N`, the map `R^{ab} →* N^{ab}` induced by the inclusion is
equivariant for conjugation by `G`. -/
theorem map_inclusion_smul (h : R ≤ N) (g : ConjAct G) (x : TopologicalAbelianization R) :
    map (Subgroup.inclusion h) (Subgroup.continuous_inclusion h) (g • x) =
      g • map (Subgroup.inclusion h) (Subgroup.continuous_inclusion h) x := by
  induction x using QuotientGroup.induction_on with | H x => ?_
  rw [MulAction.Quotient.smul_mk, map_mk, map_mk, MulAction.Quotient.smul_mk,
    Subgroup.inclusion_conj_smul]

/-- For normal subgroups `R ≤ N`, the map `R^{ab} →* N^{ab}` induced by the inclusion
intertwines the actions of `G ⧸ R` and `G ⧸ N` along the canonical map `G ⧸ R →* G ⧸ N`. -/
theorem map_inclusion_quotient_smul (h : R ≤ N) (γ : G ⧸ R) (x : TopologicalAbelianization R) :
    map (Subgroup.inclusion h) (Subgroup.continuous_inclusion h) (γ • x) =
      QuotientGroup.map R N (MonoidHom.id G) (h.trans (Subgroup.comap_id N).ge) γ •
        map (Subgroup.inclusion h) (Subgroup.continuous_inclusion h) x := by
  induction γ using QuotientGroup.induction_on with | H g => ?_
  rw [QuotientGroup.map_mk, MonoidHom.id_apply, mk_smul, mk_smul, map_inclusion_smul]

/-- For normal subgroups `R ≤ N`, the map `R^{ab} →* N^{ab}` induced by the inclusion
intertwines the actions of `G ⧸ R` and `G ⧸ N`, on the class of `g : G`. -/
theorem map_inclusion_mk_smul (h : R ≤ N) (g : G) (x : TopologicalAbelianization R) :
    map (Subgroup.inclusion h) (Subgroup.continuous_inclusion h) ((g : G ⧸ R) • x) =
      (g : G ⧸ N) • map (Subgroup.inclusion h) (Subgroup.continuous_inclusion h) x := by
  rw [map_inclusion_quotient_smul, QuotientGroup.map_mk, MonoidHom.id_apply]

end Conjugation

end TopologicalAbelianization
