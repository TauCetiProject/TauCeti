/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.TorusClass
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Bijection
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.DeckGroup
public import TauCeti.Geometry.Symplectic.Floer.SphericalPeriodGroup

/-!
# The cap cover of the contractible free loops

Let `X` be a space with homomorphisms `ω : H₂(X; ℤ) → ℝ` and `c : H₂(X; ℤ) → ℤ`, for a symplectic
manifold the symplectic area and the first Chern number, and let
`Γ = TauCeti.Floer.SphericalPeriodGroup ω c` be the quotient of the spherical classes by the joint
kernel of `ω` and `c`. Capped Hamiltonian Floer theory works on a covering space of the
contractible free loops `𝓛₀X` whose fibre over a loop is its set of caps modulo spheres of zero area
and zero first Chern number. Transporting a cap around a loop `Λ` of free loops glues to it the
torus swept out by `Λ`, so the cover is governed by the areas and first Chern numbers of these
tori.

**The period homomorphism.** A loop `Λ` of contractible free loops at the constant loop at `x`
sweeps out a torus whose class (`TauCeti.freeLoopTorusClassHom`) is spherical. Its class in `Γ`
defines a homomorphism

`π₁(𝓛₀X, x) → Γ`

(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup`), whose area and first
Chern number are those of the torus. Its kernel consists of the loops sweeping out tori of zero area
and zero first Chern number
(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff`), and it is onto
when `X` is path connected
(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective`).

**The cap cover.** The cap cover `TauCeti.Floer.CapCover ω c x` is the connected covering space of
`𝓛₀X` attached to the kernel of the period homomorphism, read on the fundamental group
(`TauCeti.Floer.capCoverSubgroup`): the quotient of the universal cover of `𝓛₀X` at the constant
loop at `x` by this subgroup. A point over a contractible loop `ℓ` is the class of a path in `𝓛₀X`
from the constant loop at `x` to `ℓ`, that is of a disc bounding `ℓ` swept out from the point `x`,
and two such discs have the same class when the closed surface they sweep out together, a torus
with spherical class, has zero area and zero first Chern number. Its projection
`TauCeti.Floer.capCoverProj` to `𝓛₀X` is a covering map as soon as `𝓛₀X` is locally path-connected
and semilocally simply connected
(`TauCeti.Floer.isCoveringMap_capCoverProj`), which holds for a locally equiconnected `X`
(`TauCeti.locallyEquiconnectedSpace_contractibleLoops`), in particular for a compact smooth
manifold, whose local equiconnectedness `Manifold.locallyEquiconnectedSpace` is a theorem rather
than an instance and must be supplied explicitly (for instance with `haveI`). So paths of
contractible loops lift uniquely, and a loop of contractible loops lifts to a loop of the cover
exactly when the torus it sweeps out has zero area and zero first Chern number
(`TauCeti.Floer.mem_range_mapOfEq_capCoverProj_iff`).

The kernel is normal, and for path-connected `X` its quotient is `Γ`, so the cap cover is regular
(`TauCeti.Floer.isRegular_capCoverProj`) with deck group `Γ`
(`TauCeti.Floer.capCoverDeckEquiv`): the period class of a loop `Λ` acts by transporting caps
around `Λ` (`TauCeti.Floer.capCoverDeckEquiv_capCoverPeriodHom_apply_mk`). Every fibre is therefore
a torsor under `Γ`: acting on any point `e` of the cover identifies `Γ` with the fibre through `e`
(`TauCeti.Floer.capCoverFiberEquiv`), so any two points of one fibre differ by a unique class of
`Γ` (`TauCeti.Floer.existsUnique_capCoverDeckEquiv_apply_eq`). This is the action of `Γ` by
recapping, on the caps of all contractible loops at once.

## Main definitions

* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup`: the period homomorphism
  `π₁(𝓛₀X, x) → Γ`, and `TauCeti.Floer.capCoverPeriodHom`, the same on the fundamental group.
* `TauCeti.Floer.capCoverSubgroup`: its kernel.
* `TauCeti.Floer.CapCover`, `TauCeti.Floer.capCoverProj`: the cap cover and its projection to
  `𝓛₀X`.
* `TauCeti.Floer.capCoverDeckEquiv`: the identification of `Γ` with the deck group of the cap
  cover.
* `TauCeti.Floer.capCoverFiberEquiv`: the identification of `Γ` with the fibre through a point.

## Main results

* `TauCeti.Floer.SphericalPeriodGroup.area_ofContractibleLoopsHomotopyGroup`,
  `TauCeti.Floer.SphericalPeriodGroup.chern_ofContractibleLoopsHomotopyGroup`: the area and first
  Chern number of the period class are those of the torus swept out by the loop.
* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff`: the kernel
  consists of the loops sweeping out tori of zero area and zero first Chern number.
* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective`: the period
  homomorphism is onto for a path-connected `X`.
* `TauCeti.Floer.isCoveringMap_capCoverProj`: the cap cover is a covering space of `𝓛₀X`.
* `TauCeti.Floer.mem_range_mapOfEq_capCoverProj_iff`: a loop of contractible loops lifts to a loop
  of the cap cover exactly when its torus has zero area and zero first Chern number.
* `TauCeti.Floer.isRegular_capCoverProj`: the cap cover is regular.
* `TauCeti.Floer.existsUnique_capCoverDeckEquiv_apply_eq`: the fibres are torsors under `Γ`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the covering space of capped loops.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3, on the covering space
  attached to a subgroup of the fundamental group.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup

namespace TauCeti.Floer.SphericalPeriodGroup

variable {X : Type} [TopologicalSpace X]
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

/-- The torus class of a loop of contractible free loops at the constant loop at `x`: the class in
`H₂(X; ℤ)` of the torus it sweeps out, through the inclusion of the contractible free loops. -/
private def contractibleTorusClassHom (x : X) :
    Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x)) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) :=
  (freeLoopTorusClassHom X (ContinuousMap.const Circle x)).comp
    (contractibleLoopsHomotopyGroupMulEquiv x).toMonoidHom.toAdditive

variable (ω c) in
/-- **The period homomorphism of the cap cover** `π₁(𝓛₀X, x) → Γ`: a loop of contractible free loops
at the constant loop at `x` goes to the class in the period group of the torus it sweeps out, which
is spherical (`TauCeti.freeLoopTorusClassHom_const_mem_sphericalClasses`). -/
def ofContractibleLoopsHomotopyGroup (x : X) :
    Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x)) →+
      SphericalPeriodGroup ω c :=
  (QuotientAddGroup.mk' _).comp ((contractibleTorusClassHom x).codRestrict _
    fun _ ↦ freeLoopTorusClassHom_const_mem_sphericalClasses x _)

/-- The area of the period class of a loop of contractible free loops is the area of the torus it
sweeps out. -/
@[simp]
theorem area_ofContractibleLoopsHomotopyGroup (x : X)
    (a : Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))) :
    PeriodGroup.area _ _ (ofContractibleLoopsHomotopyGroup ω c x a) =
      ω (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
        (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) := by
  simp [ofContractibleLoopsHomotopyGroup, contractibleTorusClassHom]

/-- The first Chern number of the period class of a loop of contractible free loops is the first
Chern number of the torus it sweeps out. -/
@[simp]
theorem chern_ofContractibleLoopsHomotopyGroup (x : X)
    (a : Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))) :
    PeriodGroup.chern _ _ (ofContractibleLoopsHomotopyGroup ω c x a) =
      c (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
        (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) := by
  simp [ofContractibleLoopsHomotopyGroup, contractibleTorusClassHom]

/-- **The kernel of the period homomorphism**, the subgroup of the cap cover: a loop of
contractible free loops has trivial period class exactly when the torus it sweeps out has zero area
and zero first Chern number. -/
theorem ofContractibleLoopsHomotopyGroup_eq_zero_iff (x : X)
    (a : Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))) :
    ofContractibleLoopsHomotopyGroup ω c x a = 0 ↔
      ω (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
          (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) = 0 ∧
        c (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
          (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) = 0 := by
  rw [PeriodGroup.ext_iff]
  simp

/-- **The period homomorphism is onto** for a path-connected space: every class of the period group
is the class of the torus swept out by a loop of contractible free loops at the constant loop at
`x`. -/
theorem ofContractibleLoopsHomotopyGroup_surjective [PathConnectedSpace X] (x : X) :
    Function.Surjective (ofContractibleLoopsHomotopyGroup ω c x) := by
  intro γ
  obtain ⟨b, rfl⟩ := ofHomotopyGroup_surjective (ω := ω) (c := c) x γ
  obtain ⟨g, hg⟩ : hurewiczIntHom X x 1 b ∈
      (freeLoopTorusClassHom X (ContinuousMap.const Circle x)).range :=
    (range_freeLoopTorusClassHom_const x).symm ▸ ⟨b, rfl⟩
  refine ⟨Additive.ofMul ((contractibleLoopsHomotopyGroupMulEquiv x).symm g.toMul),
    PeriodGroup.ext ?_ ?_⟩ <;>
    simp only [area_ofContractibleLoopsHomotopyGroup, chern_ofContractibleLoopsHomotopyGroup,
      area_ofHomotopyGroup, chern_ofHomotopyGroup, toMul_ofMul, MulEquiv.apply_symm_apply,
      ofMul_toMul, hg]

end TauCeti.Floer.SphericalPeriodGroup

/-! ### The cap cover -/

namespace TauCeti.Floer

open UniversalCover

variable {X : Type} [TopologicalSpace X]
  (ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ)
  (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ) (x : X)

/-- The period homomorphism of the cap cover, `π₁(𝓛₀X, x) → Γ`, on the fundamental group of the
contractible free loops at the constant loop at `x`, with values in `Γ` read multiplicatively. It is
`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup` through
`π₁ ≅ FundamentalGroup`. -/
def capCoverPeriodHom :
    FundamentalGroup (contractibleLoops X) (constContractibleLoop x) →*
      Multiplicative (SphericalPeriodGroup ω c) :=
  (MonoidHom.toAdditiveLeft.symm
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x)).comp
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.toMonoidHom

theorem capCoverPeriodHom_apply
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :
    capCoverPeriodHom ω c x g = Multiplicative.ofAdd
      (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g))) :=
  (rfl)

/-- The period homomorphism of the cap cover is onto for a path-connected space. -/
theorem capCoverPeriodHom_surjective [PathConnectedSpace X] :
    Function.Surjective (capCoverPeriodHom ω c x) := by
  intro γ
  obtain ⟨a, ha⟩ := SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective
    (ω := ω) (c := c) x γ.toAdd
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup a.toMul, by simp [capCoverPeriodHom_apply, ha]⟩

/-- The subgroup of the cap cover: the kernel of its period homomorphism, the loops of contractible
free loops at the constant loop at `x` that sweep out tori of zero area and zero first Chern number
(`TauCeti.Floer.mem_capCoverSubgroup_iff`). It is normal, as a kernel. -/
abbrev capCoverSubgroup :
    Subgroup (FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :=
  (capCoverPeriodHom ω c x).ker

/-- A loop of contractible free loops lies in the subgroup of the cap cover exactly when the torus
it sweeps out has zero area and zero first Chern number. -/
theorem mem_capCoverSubgroup_iff
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :
    g ∈ capCoverSubgroup ω c x ↔
      ω (freeLoopTorusClassHom X (ContinuousMap.const Circle x) (Additive.ofMul
          (contractibleLoopsHomotopyGroupMulEquiv x
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 ∧
        c (freeLoopTorusClassHom X (ContinuousMap.const Circle x) (Additive.ofMul
          (contractibleLoopsHomotopyGroupMulEquiv x
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 := by
  rw [MonoidHom.mem_ker, capCoverPeriodHom_apply, ofAdd_eq_one,
    SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff, toMul_ofMul]

/-- **The cap cover** of the contractible free loops `𝓛₀X`: the quotient of the universal cover of
`𝓛₀X` at the constant loop at `x` by `TauCeti.Floer.capCoverSubgroup`. A point over a contractible
loop `ℓ` is the class of a path in `𝓛₀X` from the constant loop at `x` to `ℓ`, a disc bounding `ℓ`
swept out from `x`; two such discs have the same class when the torus they sweep out together has
zero area and zero first Chern number. -/
abbrev CapCover : Type :=
  SubgroupQuotient (constContractibleLoop x) (capCoverSubgroup ω c x)

/-- The projection of the cap cover to the contractible free loops, the end point of a path of
loops. -/
def capCoverProj : CapCover ω c x → contractibleLoops X :=
  subgroupQuotientProj _ _

/-- The projection of the cap cover is the projection of the cover attached to
`TauCeti.Floer.capCoverSubgroup`. -/
theorem capCoverProj_def :
    capCoverProj ω c x =
      subgroupQuotientProj (constContractibleLoop x) (capCoverSubgroup ω c x) :=
  (rfl)

/-- The cap cover projects the class of a path of contractible loops to its end point. -/
@[simp]
theorem capCoverProj_mk (e : UniversalCover (constContractibleLoop x)) :
    capCoverProj ω c x (Quotient.mk'' e) = UniversalCover.proj e :=
  subgroupQuotientProj_mk _ _ e

/-- The base point of the cap cover, the class of the constant path at the constant loop at `x`:
the trivial cap of that constant loop. -/
def CapCover.basepoint : CapCover ω c x :=
  SubgroupQuotient.basepoint _ _

/-- The base point of the cap cover is the class of the constant path at the constant loop at
`x`. -/
@[simp]
theorem CapCover.basepoint_eq_mk :
    CapCover.basepoint ω c x =
      Quotient.mk'' (UniversalCover.mk _ (Path.Homotopic.Quotient.refl _)) :=
  SubgroupQuotient.basepoint_eq_mk _ _

theorem capCoverProj_basepoint :
    capCoverProj ω c x (CapCover.basepoint ω c x) = constContractibleLoop x :=
  subgroupQuotientProj_basepoint _ _

theorem continuous_capCoverProj : Continuous (capCoverProj ω c x) :=
  continuous_subgroupQuotientProj _ _

/-- Every contractible free loop of a path-connected space has a cap: the projection of the cap
cover is onto. -/
theorem capCoverProj_surjective [PathConnectedSpace X] :
    Function.Surjective (capCoverProj ω c x) :=
  subgroupQuotientProj_surjective _ _

variable [LocallyPathConnectedSpace (contractibleLoops X)]
  [SemilocallySimplyConnectedSpace (contractibleLoops X)]

/-- **The cap cover is a covering space** of the contractible free loops, as soon as these are
locally path-connected and semilocally simply connected, for instance for a locally equiconnected
space `X` such as a compact smooth manifold. -/
theorem isCoveringMap_capCoverProj : IsCoveringMap (capCoverProj ω c x) :=
  isCoveringMap_subgroupQuotientProj _ _

/-- **A loop of contractible free loops lifts to a loop of the cap cover**, at its base point,
exactly when the torus it sweeps out has zero area and zero first Chern number: the subgroup of
`π₁(𝓛₀X)` recovered by the cap cover is `TauCeti.Floer.capCoverSubgroup`. -/
theorem mem_range_mapOfEq_capCoverProj_iff
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :
    g ∈ (FundamentalGroup.mapOfEq ⟨capCoverProj ω c x, continuous_capCoverProj ω c x⟩
        (capCoverProj_basepoint ω c x)).range ↔
      ω (freeLoopTorusClassHom X (ContinuousMap.const Circle x) (Additive.ofMul
          (contractibleLoopsHomotopyGroupMulEquiv x
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 ∧
        c (freeLoopTorusClassHom X (ContinuousMap.const Circle x) (Additive.ofMul
          (contractibleLoopsHomotopyGroupMulEquiv x
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 := by
  rw [← mem_capCoverSubgroup_iff]
  exact SetLike.ext_iff.1 (range_mapOfEq_subgroupQuotientProj _ _) g

variable [PathConnectedSpace X]

/-- **The deck group of the cap cover is the period group** `Γ`, for a path-connected space: the
deck group of the cover attached to the normal subgroup `capCoverSubgroup` is the quotient of
`π₁(𝓛₀X)` by it, which the period homomorphism identifies with `Γ`. -/
def capCoverDeckEquiv :
    Multiplicative (SphericalPeriodGroup ω c) ≃* deck (capCoverProj ω c x) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (capCoverPeriodHom_surjective ω c x)).symm.trans
    (deckSubgroupQuotientProjEquivOfNormal _ _)

/-- The period class of a loop `g` of contractible free loops acts on the cap cover by transporting
caps around `g`: it sends the class of a path `e` of loops to the class of `g • e`. -/
@[simp]
theorem capCoverDeckEquiv_capCoverPeriodHom_apply_mk
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x))
    (e : UniversalCover (constContractibleLoop x)) :
    (capCoverDeckEquiv ω c x (capCoverPeriodHom ω c x g) : CapCover ω c x ≃ₜ CapCover ω c x)
        (Quotient.mk'' e) = Quotient.mk'' (g • e) := by
  have hg : (QuotientGroup.quotientKerEquivOfSurjective _ (capCoverPeriodHom_surjective ω c x)).symm
      (capCoverPeriodHom ω c x g) = QuotientGroup.mk g :=
    (MulEquiv.symm_apply_eq _).2 rfl
  have h := deckSubgroupQuotientProjEquivOfNormal_mk_apply (constContractibleLoop x)
    (capCoverSubgroup ω c x) g e
  rw [← hg] at h
  -- `capCoverProj` is `subgroupQuotientProj` by definition, so the two deck groups are the same
  -- subgroup and `h` is the goal once `capCoverDeckEquiv` is unfolded to its defining composite.
  exact h

/-- The inverse of the deck transformation of the period class of a loop `g` of contractible free
loops sends the class of a path `e` of loops to the class of `g⁻¹ • e`. -/
@[simp]
theorem capCoverDeckEquiv_capCoverPeriodHom_symm_apply_mk
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x))
    (e : UniversalCover (constContractibleLoop x)) :
    (capCoverDeckEquiv ω c x (capCoverPeriodHom ω c x g) : CapCover ω c x ≃ₜ CapCover ω c x).symm
        (Quotient.mk'' e) = Quotient.mk'' (g⁻¹ • e) := by
  have hg : (QuotientGroup.quotientKerEquivOfSurjective _ (capCoverPeriodHom_surjective ω c x)).symm
      (capCoverPeriodHom ω c x g) = QuotientGroup.mk g :=
    (MulEquiv.symm_apply_eq _).2 rfl
  have h := deckSubgroupQuotientProjEquivOfNormal_mk_symm_apply (constContractibleLoop x)
    (capCoverSubgroup ω c x) g e
  rw [← hg] at h
  exact h

/-- **The cap cover is a regular cover**: its deck group acts transitively on every fibre. -/
theorem isRegular_capCoverProj : Deck.IsRegular (capCoverProj ω c x) :=
  (isRegular_subgroupQuotientProj_iff_normal _ _).2 inferInstance

/-- **The fibres of the cap cover are torsors under the period group**: acting on a point `e` of the
cap cover identifies `Γ` with the fibre through `e`, a class `γ` going to the image of `e` under the
deck transformation of `γ`. -/
def capCoverFiberEquiv (e : CapCover ω c x) :
    SphericalPeriodGroup ω c ≃ capCoverProj ω c x ⁻¹' {capCoverProj ω c x e} :=
  (Multiplicative.ofAdd.trans (capCoverDeckEquiv ω c x).toEquiv).trans
    (Deck.deckEquivFiber (isCoveringMap_capCoverProj ω c x) (isRegular_capCoverProj ω c x)
      ⟨e, rfl⟩)

@[simp]
theorem coe_capCoverFiberEquiv_apply (e : CapCover ω c x) (γ : SphericalPeriodGroup ω c) :
    (capCoverFiberEquiv ω c x e γ : CapCover ω c x) =
      (capCoverDeckEquiv ω c x (Multiplicative.ofAdd γ) : CapCover ω c x ≃ₜ CapCover ω c x) e :=
  Deck.deckEquivFiber_apply_coe (isCoveringMap_capCoverProj ω c x) (isRegular_capCoverProj ω c x)
    ⟨e, rfl⟩ _

/-- Any two points of one fibre of the cap cover differ by a unique class of the period group. -/
theorem existsUnique_capCoverDeckEquiv_apply_eq {e e' : CapCover ω c x}
    (h : capCoverProj ω c x e = capCoverProj ω c x e') :
    ∃! γ : SphericalPeriodGroup ω c,
      (capCoverDeckEquiv ω c x (Multiplicative.ofAdd γ) : CapCover ω c x ≃ₜ CapCover ω c x) e =
        e' := by
  obtain ⟨γ, hγ, huniq⟩ := (capCoverFiberEquiv ω c x e).bijective.existsUnique ⟨e', h.symm⟩
  refine ⟨γ, (coe_capCoverFiberEquiv_apply ω c x e γ).symm.trans (congrArg Subtype.val hγ),
    fun γ' hγ' ↦ huniq γ' (Subtype.ext ?_)⟩
  exact (coe_capCoverFiberEquiv_apply ω c x e γ').trans hγ'

end TauCeti.Floer
