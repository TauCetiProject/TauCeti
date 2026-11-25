/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.TorusClass
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.AdditiveKer
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Floer.SphericalPeriodGroup

/-!
# The cap cover of the contractible free loops

Let `X` be a space with homomorphisms `ω : H₂(X; ℤ) → ℝ` and `c : H₂(X; ℤ) → ℤ`, for a symplectic
manifold the symplectic area and the first Chern number, and let
`Γ = TauCeti.Floer.SphericalPeriodGroup ω c` be the quotient of the spherical classes by the joint
kernel of `ω` and `c`. Capped Hamiltonian Floer theory works on the covering space of the
contractible free loops `𝓛₀X` whose fibre over a loop is its set of caps modulo spheres of zero area
and zero first Chern number. Transporting a cap around a loop `Λ` of free loops glues to it the
torus swept out by `Λ`, so the cover is governed by the areas and first Chern numbers of these
tori.

The period/Chern transgression of loops of contractible free loops factors through `Γ`. A loop `Λ`
of contractible free loops at the constant loop at `x` sweeps out a torus whose class
(`TauCeti.freeLoopTorusClassHom`) is spherical. Its class in `Γ` defines a homomorphism

`π₁(𝓛₀X, x) → Γ`

(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup`), whose area and first
Chern number are those of the torus. Its kernel consists of the loops sweeping out tori of zero area
and zero first Chern number
(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff`), and it is onto
when `X` is path connected
(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective`).

The **cap cover** `TauCeti.Floer.CapCover ω c x` is the connected covering space of `𝓛₀X`
attached to this kernel (`TauCeti.Floer.capCoverSubgroup`), the quotient of the universal cover of
`𝓛₀X` by it. A point over a loop `γ` is a homotopy class of paths in `𝓛₀X` from the constant loop
at `x` to `γ`, modulo loops sweeping out tori of zero area and zero first Chern number. When `𝓛₀X`
is locally path-connected and semilocally simply connected, for instance when `X` is locally
equiconnected, such as a closed manifold, the projection is a covering map
(`TauCeti.Floer.isCoveringMap_capCoverProj`), so paths and their homotopies in `𝓛₀X` lift, and a
loop of contractible loops lifts to a loop of the cover exactly when the torus it sweeps out has
zero area and zero first Chern number (`TauCeti.Floer.mem_range_mapOfEq_capCoverProj_iff`). The
kernel is normal, and over a path-connected `X` the cover is regular, with deck group `Γ`
(`TauCeti.Floer.capCoverDeckEquiv`): the period class of a loop `Λ` acts by transport around `Λ`
(`TauCeti.Floer.capCoverDeckEquiv_capCoverPeriodHom_apply_mk`,
`TauCeti.Floer.ofContractibleLoopsHomotopyGroup_vadd_mk`). So `Γ` acts on the cap cover, and every
fibre is a torsor under `Γ` (`TauCeti.Floer.instAddTorsorCapCoverFiber`): the difference of two
points of a fibre is the period class of the loop relating them (`TauCeti.Floer.CapCover.vsub_mk`).
The cap classes of a contractible loop are also a `Γ`-torsor
(`TauCeti.Floer.SphericalCapClass.instAddTorsor`), where `Γ` acts by gluing spheres at the centre
of a cap. A class `a ∈ π₂(X, x)`, read as a loop of based loops at the constant loop, has period
class the class of `a` in `Γ`
(`SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_contractibleLoopHomotopyGroupHom`).

**The fibre over a based loop is its set of cap classes.** A raw cap `D` of a loop `γ` at `x` is
the class of a path in `Ω X x` from `γ` to the constant loop. Run backwards and read in the
contractible free loops, it is a path from the constant loop at `x` to `γ`, so it gives a point of
the cap cover over `γ` (`TauCeti.Floer.RawCap.toCapCover`). Gluing a sphere `a ∈ π₂(X, x)` at the
centre of the disc prepends to this path the loop of free loops swept by the sphere, whose torus
class is the Hurewicz class of `a` (`TauCeti.freeLoopTorusClassHom_eq_hurewiczIntHom`). So the
point moves by the class of `a` in `Γ` (`TauCeti.Floer.RawCap.toCapCover_vadd`). In particular the
point depends only on the cap class (`TauCeti.Floer.SphericalCapClass.toCapCover`), and, both being
`Γ`-torsors, the cap classes of `γ` are in bijection with the fibre over `γ`
(`TauCeti.Floer.SphericalCapClass.capCoverFiberEquiv`). The bijection carries recapping by `g` to
the deck transformation of `g` (`TauCeti.Floer.SphericalCapClass.capCoverFiberEquiv_vadd`).

## Main definitions

* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup`: the period homomorphism
  `π₁(𝓛₀X, x) → Γ`, and `TauCeti.Floer.capCoverPeriodHom`, the same on the fundamental group.
* `TauCeti.Floer.capCoverSubgroup`: its kernel, read in the fundamental group of `𝓛₀X`.
* `TauCeti.Floer.CapCover`, `TauCeti.Floer.capCoverProj`: the cap cover and its projection to
  `𝓛₀X`.
* `TauCeti.Floer.capCoverDeckEquiv`: the deck group of the cap cover is `Γ`.
* `TauCeti.Floer.instAddActionCapCover`, `TauCeti.Floer.instAddTorsorCapCoverFiber`: `Γ` acts on
  the cap cover, and each fibre is a `Γ`-torsor.
* `TauCeti.Floer.RawCap.toCapCover`, `TauCeti.Floer.SphericalCapClass.toCapCover`: the point of the
  cap cover of a raw cap and of a cap class.
* `TauCeti.Floer.SphericalCapClass.capCoverFiberEquiv`: the cap classes of a contractible loop at
  `x` are the fibre of the cap cover over it.

## Main results

* `TauCeti.Floer.SphericalPeriodGroup.area_ofContractibleLoopsHomotopyGroup`,
  `TauCeti.Floer.SphericalPeriodGroup.chern_ofContractibleLoopsHomotopyGroup`: the area and first
  Chern number of the period class of a loop are those of the torus it sweeps out.
* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff`: the kernel of
  the period homomorphism consists of the loops sweeping out tori of zero area and zero first Chern
  number.
* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective`: the period
  homomorphism is onto for a path-connected `X`.
* `SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_contractibleLoopHomotopyGroupHom`: the
  period class of a sphere, read as a loop of based loops, is its class in the period group.
* `TauCeti.Floer.isCoveringMap_capCoverProj`, `TauCeti.Floer.isRegular_capCoverProj`: the cap
  cover is a covering space, regular over a path-connected `X`.
* `TauCeti.Floer.mem_range_mapOfEq_capCoverProj_iff`: a loop of contractible loops lifts to a loop
  of the cap cover exactly when its torus has zero area and zero first Chern number.
* `TauCeti.Floer.ofContractibleLoopsHomotopyGroup_vadd_mk`: the period class of a loop of
  contractible free loops acts on the cap cover as the loop acts on the universal cover.
* `TauCeti.Floer.CapCover.vsub_mk`: the difference of two points of a fibre is the period class of
  the loop relating them.
* `TauCeti.Floer.RawCap.toCapCover_vadd`, `TauCeti.Floer.SphericalCapClass.toCapCover_vadd`,
  `TauCeti.Floer.SphericalCapClass.capCoverFiberEquiv_vadd`: recapping by `g` moves the point of
  the cap cover by `g`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the covering space of capped loops.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
* A. Hatcher, *Algebraic Topology*, Section 1.3, on the covering space attached to a subgroup of
  the fundamental group and its deck group.
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

/-- **The period class of a sphere read as a loop of contractible loops is its class in the
period group.** A class `a ∈ π₂(X, x)` is a loop at the constant loop of based loops at `x`
(`TauCeti.contractibleLoopHomotopyGroupHom`), hence of contractible free loops; its period class is
the class of the sphere `a`, since the torus it sweeps out has the Hurewicz class of `a`
(`TauCeti.freeLoopTorusClassHom_freeLoopHomotopyGroupHom`). -/
@[simp]
theorem ofContractibleLoopsHomotopyGroup_contractibleLoopHomotopyGroupHom (x : X)
    (a : HomotopyGroup (Fin 2) X x) :
    ofContractibleLoopsHomotopyGroup ω c x
        (Additive.ofMul (contractibleLoopHomotopyGroupHom x 0 a)) =
      ofHomotopyGroup ω c x (Additive.ofMul a) := by
  refine PeriodGroup.ext ?_ ?_ <;>
    simp only [area_ofContractibleLoopsHomotopyGroup, chern_ofContractibleLoopsHomotopyGroup,
      toMul_ofMul, contractibleLoopsHomotopyGroupMulEquiv_contractibleLoopHomotopyGroupHom,
      freeLoopTorusClassHom_freeLoopHomotopyGroupHom, area_ofHomotopyGroup, chern_ofHomotopyGroup]

end TauCeti.Floer.SphericalPeriodGroup

/-! ### The cap cover -/

namespace TauCeti.Floer

open TauCeti.UniversalCover

variable {X : Type} [TopologicalSpace X]
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

variable (ω c) in
/-- **The period homomorphism of the cap cover** on the fundamental group of `𝓛₀X` at the constant
loop at `x`, with values in `Γ` read multiplicatively: it is
`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup` through
`π₁ ≅ FundamentalGroup` (`TauCeti.UniversalCover.fundamentalGroupHomOfAdditive`). -/
def capCoverPeriodHom (x : X) :
    FundamentalGroup (contractibleLoops X) (constContractibleLoop x) →*
      Multiplicative (SphericalPeriodGroup ω c) :=
  fundamentalGroupHomOfAdditive _ (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x)

theorem capCoverPeriodHom_apply (x : X)
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :
    capCoverPeriodHom ω c x g = Multiplicative.ofAdd
      (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g))) :=
  fundamentalGroupHomOfAdditive_apply _ _ g

@[simp]
theorem capCoverPeriodHom_pi1MulEquivFundamentalGroup (x : X)
    (a : HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x)) :
    capCoverPeriodHom ω c x (HomotopyGroup.pi1MulEquivFundamentalGroup a) =
      Multiplicative.ofAdd
        (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x (Additive.ofMul a)) :=
  fundamentalGroupHomOfAdditive_pi1MulEquivFundamentalGroup _ _ a

/-- The period homomorphism of the cap cover is onto for a path-connected space. -/
theorem capCoverPeriodHom_surjective [PathConnectedSpace X] (x : X) :
    Function.Surjective (capCoverPeriodHom ω c x) :=
  fundamentalGroupHomOfAdditive_surjective _ _
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective x)

variable (ω c) in
/-- **The subgroup of the cap cover**: the classes in `π₁(𝓛₀X, x)`, at the constant loop at `x`,
of the loops of contractible free loops sweeping out tori of zero area and zero first Chern
number, the kernel of the period homomorphism
`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup`. -/
def capCoverSubgroup (x : X) :
    Subgroup (FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :=
  additiveKerSubgroup (constContractibleLoop x)
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x)

/-- A class of `π₁(𝓛₀X, x)` lies in the subgroup of the cap cover exactly when its period class
vanishes. -/
@[simp]
theorem mem_capCoverSubgroup_iff (x : X)
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :
    g ∈ capCoverSubgroup ω c x ↔
      SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)) = 0 :=
  mem_additiveKerSubgroup_iff _ _ g

/-- The subgroup of the cap cover is normal, being the kernel of a homomorphism. -/
instance capCoverSubgroup_normal (x : X) : (capCoverSubgroup ω c x).Normal :=
  additiveKerSubgroup_normal _ _

variable (ω c) in
/-- **The cap cover** of the contractible free loops `𝓛₀X`: the connected covering space of the
path component of the constant loop at `x` attached to the subgroup `capCoverSubgroup ω c x` of
`π₁(𝓛₀X, x)`. A point over a loop `γ` is a homotopy class of paths in `𝓛₀X` from the constant loop
at `x` to `γ`, modulo loops sweeping out tori of zero area and zero first Chern number. -/
abbrev CapCover (x : X) : Type :=
  SubgroupQuotient (constContractibleLoop x) (capCoverSubgroup ω c x)

variable (ω c) in
/-- The projection of the cap cover to the contractible free loops. -/
abbrev capCoverProj (x : X) : CapCover ω c x → contractibleLoops X :=
  subgroupQuotientProj (constContractibleLoop x) (capCoverSubgroup ω c x)

/-- **The cap cover is a covering space** of `𝓛₀X`, for instance when `X` is locally
equiconnected, such as a closed manifold. -/
theorem isCoveringMap_capCoverProj [LocallyPathConnectedSpace (contractibleLoops X)]
    [SemilocallySimplyConnectedSpace (contractibleLoops X)] (x : X) :
    IsCoveringMap (capCoverProj ω c x) :=
  isCoveringMap_subgroupQuotientProj _ _

/-- **A loop of contractible free loops lifts to a loop of the cap cover**, at its base point,
exactly when the torus it sweeps out has zero area and zero first Chern number: the subgroup of
`π₁(𝓛₀X)` recovered by the cap cover is `TauCeti.Floer.capCoverSubgroup`. -/
theorem mem_range_mapOfEq_capCoverProj_iff [LocallyPathConnectedSpace (contractibleLoops X)]
    [SemilocallySimplyConnectedSpace (contractibleLoops X)] (x : X)
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x)) :
    g ∈ (FundamentalGroup.mapOfEq
        ⟨capCoverProj ω c x, continuous_subgroupQuotientProj _ _⟩
        (subgroupQuotientProj_basepoint _ _)).range ↔
      ω (freeLoopTorusClassHom X (ContinuousMap.const Circle x) (Additive.ofMul
          (contractibleLoopsHomotopyGroupMulEquiv x
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 ∧
        c (freeLoopTorusClassHom X (ContinuousMap.const Circle x) (Additive.ofMul
          (contractibleLoopsHomotopyGroupMulEquiv x
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 := by
  rw [range_mapOfEq_subgroupQuotientProj, mem_capCoverSubgroup_iff,
    SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff, toMul_ofMul]

/-- The cap cover over a path-connected space is a regular covering. -/
theorem isRegular_capCoverProj [PathConnectedSpace X]
    [LocallyPathConnectedSpace (contractibleLoops X)]
    [SemilocallySimplyConnectedSpace (contractibleLoops X)] (x : X) :
    Deck.IsRegular (capCoverProj ω c x) :=
  (isRegular_subgroupQuotientProj_iff_normal _ _).mpr inferInstance

section Deck

variable [PathConnectedSpace X] [LocallyPathConnectedSpace (contractibleLoops X)]
  [SemilocallySimplyConnectedSpace (contractibleLoops X)]

variable (ω c) in
/-- **The deck group of the cap cover is the spherical period group** `Γ`: the period
homomorphism `π₁(𝓛₀X, x) → Γ` is onto with kernel `capCoverSubgroup ω c x`, and the deck group of
the cover attached to the kernel of a surjective homomorphism is its target. -/
def capCoverDeckEquiv (x : X) :
    Multiplicative (SphericalPeriodGroup ω c) ≃* deck (capCoverProj ω c x) :=
  deckAdditiveKerEquiv _ _ (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective x)

/-- The period class of a loop `g` of contractible free loops acts on the cap cover by transporting
caps around `g`: it sends the class of a path `e` of loops to the class of `g • e`. -/
@[simp]
theorem capCoverDeckEquiv_capCoverPeriodHom_apply_mk (x : X)
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x))
    (e : UniversalCover (constContractibleLoop x)) :
    (capCoverDeckEquiv ω c x (capCoverPeriodHom ω c x g)).val (Quotient.mk'' e) =
      Quotient.mk'' (g • e) :=
  deckAdditiveKerEquiv_fundamentalGroupHomOfAdditive_apply_mk _ _
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective x) g e

/-- The inverse of the deck transformation of the period class of a loop `g` of contractible free
loops sends the class of a path `e` of loops to the class of `g⁻¹ • e`. -/
@[simp]
theorem capCoverDeckEquiv_capCoverPeriodHom_symm_apply_mk (x : X)
    (g : FundamentalGroup (contractibleLoops X) (constContractibleLoop x))
    (e : UniversalCover (constContractibleLoop x)) :
    (capCoverDeckEquiv ω c x (capCoverPeriodHom ω c x g)).val.symm (Quotient.mk'' e) =
      Quotient.mk'' (g⁻¹ • e) :=
  deckAdditiveKerEquiv_fundamentalGroupHomOfAdditive_symm_apply_mk _ _
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective x) g e

/-- The deck transformation of the period class of a loop `a` of contractible free loops acts on
the cap cover through the action of `a` on the universal cover of `𝓛₀X`. -/
@[simp]
theorem capCoverDeckEquiv_ofContractibleLoopsHomotopyGroup_apply_mk (x : X)
    (a : HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))
    (e : UniversalCover (constContractibleLoop x)) :
    (capCoverDeckEquiv ω c x (Multiplicative.ofAdd
        (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x (Additive.ofMul a)))).val
        (Quotient.mk'' e) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :=
  deckAdditiveKerEquiv_apply_mk _ _
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective x) a e

/-- The spherical period group `Γ` acts on the cap cover through its deck group. -/
noncomputable instance instAddActionCapCover :
    AddAction (SphericalPeriodGroup ω c) (CapCover ω c x) :=
  Deck.addActionOfMulEquiv (capCoverDeckEquiv ω c x)

namespace CapCover

/-- The spherical period group acts on the cap cover by the deck transformations of
`capCoverDeckEquiv`. -/
theorem vadd_def (g : SphericalPeriodGroup ω c) (e : CapCover ω c x) :
    g +ᵥ e = (capCoverDeckEquiv ω c x (Multiplicative.ofAdd g)).val e :=
  Deck.addActionOfMulEquiv_vadd (capCoverDeckEquiv ω c x) g e

end CapCover

open CapCover

/-- The action of the spherical period group preserves the projection of the cap cover. -/
@[simp]
theorem capCoverProj_vadd (g : SphericalPeriodGroup ω c) (e : CapCover ω c x) :
    capCoverProj ω c x (g +ᵥ e) = capCoverProj ω c x e :=
  Deck.proj_addActionOfMulEquiv_vadd (capCoverDeckEquiv ω c x) g e

/-- **Transporting a point of the cap cover around a loop of contractible free loops adds the
period class of the torus it sweeps out**: the period class of `a ∈ π₁(𝓛₀X, x)` acts on the cap
cover as `a` acts on the universal cover of `𝓛₀X`. -/
@[simp]
theorem ofContractibleLoopsHomotopyGroup_vadd_mk
    (a : HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))
    (e : UniversalCover (constContractibleLoop x)) :
    SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x (Additive.ofMul a) +ᵥ
        (Quotient.mk'' e : CapCover ω c x) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :=
  deckAdditiveKerEquiv_vadd_mk _ _
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective x) a e

/-- **Each fibre of the cap cover is a torsor under the spherical period group** `Γ`: the deck
group `Γ` of the regular cover acts simply transitively on every fibre. -/
noncomputable instance instAddTorsorCapCoverFiber (γ : contractibleLoops X) :
    AddTorsor (SphericalPeriodGroup ω c) (capCoverProj ω c x ⁻¹' {γ}) :=
  Deck.fiberAddTorsorOfMulEquiv (isCoveringMap_capCoverProj x) (isRegular_capCoverProj x)
    (capCoverDeckEquiv ω c x) γ

/-- The action of the spherical period group on a fibre of the cap cover is its action on the
cap cover. -/
@[simp]
theorem CapCover.coe_vadd_fiber {γ : contractibleLoops X} (g : SphericalPeriodGroup ω c)
    (e : capCoverProj ω c x ⁻¹' {γ}) :
    ((g +ᵥ e : capCoverProj ω c x ⁻¹' {γ}) : CapCover ω c x) = g +ᵥ (e : CapCover ω c x) :=
  Deck.coe_fiberAddTorsorOfMulEquiv_vadd _ _ (capCoverDeckEquiv ω c x) g e

/-- The difference of two points of a fibre of the cap cover carries the second to the first on
the cap cover. -/
@[simp]
theorem CapCover.vsub_vadd_coe {γ : contractibleLoops X} (e₁ e₂ : capCoverProj ω c x ⁻¹' {γ}) :
    (e₁ -ᵥ e₂) +ᵥ (e₂ : CapCover ω c x) = e₁ := by
  rw [← coe_vadd_fiber, vsub_vadd]

/-- **The difference of two points of a fibre of the cap cover is the period class of the loop
relating them**: transporting `e` around a loop `a` of contractible free loops gives the point
whose difference from `e` is the period class of `a`. -/
@[simp]
theorem CapCover.vsub_mk {γ : contractibleLoops X}
    (a : HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))
    (e : UniversalCover (constContractibleLoop x))
    (h₁ : (Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) : CapCover ω c x) ∈
      capCoverProj ω c x ⁻¹' {γ})
    (h₂ : (Quotient.mk'' e : CapCover ω c x) ∈ capCoverProj ω c x ⁻¹' {γ}) :
    (⟨_, h₁⟩ : capCoverProj ω c x ⁻¹' {γ}) -ᵥ ⟨_, h₂⟩ =
      SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x (Additive.ofMul a) :=
  deckAdditiveKerEquiv_vsub_mk _ _
    (SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective x) a e h₁ h₂

end Deck

/-! ### The fibre over a based loop and its cap classes -/

section Fiber

open scoped Topology unitInterval Topology.Homotopy

variable {x : X} {γ : Ω X x}

/-- The path component of the constant loop at `x` consists of contractible free loops. -/
private theorem pathComponent_constContractibleLoop_subset (x : X) :
    pathComponent ((constContractibleLoop x : contractibleLoops X) : C(Circle, X)) ⊆
      contractibleLoops X := by
  rw [coe_constContractibleLoop]
  exact pathComponent_const_subset_contractibleLoops x

/-- **A loop with a raw cap is a contractible free loop**: the cap, read in the free loops, joins
`γ` to the constant loop at `x`. -/
theorem RawCap.toCircle_mem_contractibleLoops (D : RawCap γ) :
    γ.toCircle ∈ contractibleLoops X :=
  mem_contractibleLoops_iff.2
    ⟨x, ⟨(D.out.map (Path.continuous_toCircle x)).cast rfl (Path.toCircle_refl x).symm⟩⟩

/-- **A loop with a cap class is a contractible free loop.** -/
theorem SphericalCapClass.toCircle_mem_contractibleLoops (q : SphericalCapClass ω c γ) :
    γ.toCircle ∈ contractibleLoops X :=
  (mk_surjective q).elim fun D _ ↦ D.toCircle_mem_contractibleLoops

/-- The path of free loops traced by a disc `p` bounding `γ`, run from its centre to `γ`. -/
private def capFreeLoopPath (p : Path γ (Path.refl x)) :
    Path ((constContractibleLoop x : contractibleLoops X) : C(Circle, X)) γ.toCircle :=
  (p.symm.map (Path.continuous_toCircle x)).cast
    (by simp only [coe_constContractibleLoop, Path.toCircle_refl]) rfl

/-- The path of contractible free loops traced by a disc `p` bounding `γ`, run from its centre to
`γ`. -/
def capCoverPath (hγ : γ.toCircle ∈ contractibleLoops X) (p : Path γ (Path.refl x)) :
    Path (constContractibleLoop x) (⟨γ.toCircle, hγ⟩ : contractibleLoops X) :=
  (Path.subtypeHomeomorphOfPathComponentSubset
    (pathComponent_constContractibleLoop_subset x)).symm (capFreeLoopPath p)

/-- The loop of contractible free loops traced by a double loop `β` at the constant loop. -/
private def sphereLoopPath (β : Ω (Ω X x) (Path.refl x)) :
    Path (constContractibleLoop x) (constContractibleLoop x) :=
  (Path.subtypeHomeomorphOfPathComponentSubset
    (pathComponent_constContractibleLoop_subset x)).symm
      ((β.map (Path.continuous_toCircle x)).cast
        (by simp only [coe_constContractibleLoop, Path.toCircle_refl])
        (by simp only [coe_constContractibleLoop, Path.toCircle_refl]))

/-- The path of contractible free loops of a disc, read in the free loops, is its path of free
loops. -/
private theorem map_subtypeVal_capCoverPath (hγ : γ.toCircle ∈ contractibleLoops X)
    (p : Path γ (Path.refl x)) :
    (capCoverPath hγ p).map continuous_subtypeVal = capFreeLoopPath p :=
  Path.ext <| funext fun t ↦ by
    rw [capCoverPath, Path.map_coe, Function.comp_apply,
      Path.coe_subtypeHomeomorphOfPathComponentSubset_symm_apply]

/-- At time `t`, the path of contractible free loops of a disc `p` is the free loop of
`p (σ t)`. -/
@[simp]
theorem coe_capCoverPath_apply (hγ : γ.toCircle ∈ contractibleLoops X)
    (p : Path γ (Path.refl x)) (t : I) :
    (capCoverPath hγ p t : C(Circle, X)) = (p (σ t)).toCircle := by
  rw [capCoverPath, Path.coe_subtypeHomeomorphOfPathComponentSubset_symm_apply, capFreeLoopPath]
  simp

private theorem coe_sphereLoopPath_apply (β : Ω (Ω X x) (Path.refl x)) (t : I) :
    (sphereLoopPath β t : C(Circle, X)) = (β t).toCircle := by
  rw [sphereLoopPath, Path.coe_subtypeHomeomorphOfPathComponentSubset_symm_apply]
  simp

/-- Gluing a sphere at the centre of a disc prepends the reversed loop of free loops of the
sphere to the path of the disc. -/
private theorem capCoverPath_trans (hγ : γ.toCircle ∈ contractibleLoops X)
    (p : Path γ (Path.refl x)) (β : Ω (Ω X x) (Path.refl x)) :
    capCoverPath hγ (p.trans β) = (sphereLoopPath β).symm.trans (capCoverPath hγ p) := by
  refine Path.ext (funext fun t ↦ Subtype.ext ?_)
  rw [coe_capCoverPath_apply, Path.trans_apply, Path.trans_apply]
  -- Both sides follow `β` backwards on `[0, 1/2]` and `p` backwards on `[1/2, 1]`; at `t = 1/2`
  -- both are at the constant loop.
  split_ifs with h₁ h₂ h₂ <;>
    simp only [Path.symm_apply, Function.comp_apply, coe_sphereLoopPath_apply,
      coe_capCoverPath_apply, unitInterval.coe_symm_eq] at h₁ ⊢
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    trans (Path.refl x).toCircle
    · congr 1
      convert p.target using 2
      ext
      norm_num [ht]
    · congr 1
      convert β.source.symm using 2
      ext
      simp [ht]
  · congr 2
    ext
    simp only [unitInterval.coe_symm_eq]
    ring
  · congr 2
    ext
    simp only [unitInterval.coe_symm_eq]
    ring
  · exfalso
    linarith

variable (ω c) in
/-- **The point of the cap cover of a raw cap.** A raw cap `D` of a loop `γ` at `x` is the class of
a path in `Ω X x` from `γ` to the constant loop, a disc bounding `γ`. Run backwards and read in the
contractible free loops, it is a path from the constant loop at `x` to `γ`, whose class is a point
of the cap cover over `γ`. -/
def RawCap.toCapCover (D : RawCap γ) : CapCover ω c x :=
  Quotient.mk'' (UniversalCover.mk ⟨γ.toCircle, D.toCircle_mem_contractibleLoops⟩
    (Quotient.map (capCoverPath D.toCircle_mem_contractibleLoops)
    (fun p q h ↦ homotopic_of_map_subtypeVal_homotopic_of_pathComponent_subset
      (pathComponent_constContractibleLoop_subset x) <| by
        rw [map_subtypeVal_capCoverPath, map_subtypeVal_capCoverPath]
        exact ((Path.Homotopic.symm₂ h).map ⟨_, Path.continuous_toCircle x⟩).pathCast _ _)
    D))

/-- The point of the cap cover of the class of a disc `p` is the class of its path of free loops. -/
theorem RawCap.toCapCover_mk (p : Path γ (Path.refl x)) :
    RawCap.toCapCover ω c (Path.Homotopic.Quotient.mk p) =
      Quotient.mk'' (UniversalCover.mk
        ⟨γ.toCircle, toCircle_mem_contractibleLoops (Path.Homotopic.Quotient.mk p)⟩
        (Path.Homotopic.Quotient.mk
          (capCoverPath (toCircle_mem_contractibleLoops (Path.Homotopic.Quotient.mk p)) p))) :=
  (rfl)

/-- The point of the cap cover of a raw cap of `γ` lies over `γ`. -/
@[simp]
theorem RawCap.capCoverProj_toCapCover (D : RawCap γ) :
    capCoverProj ω c x (D.toCapCover ω c) = ⟨γ.toCircle, D.toCircle_mem_contractibleLoops⟩ := by
  rw [RawCap.toCapCover]
  exact subgroupQuotientProj_mk _ _ _

/-- The period class of the loop of contractible free loops traced by a double loop `β` is the
class of the sphere of `β`. -/
private theorem ofContractibleLoopsHomotopyGroup_sphereLoopPath (β : Ω (Ω X x) (Path.refl x)) :
    SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup ω c x
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (sphereLoopPath β))))) =
      SphericalPeriodGroup.ofHomotopyGroup ω c x
        (Additive.ofMul (HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))) := by
  have htorus := freeLoopTorusClassHom_eq_hurewiczIntHom β
    (GenLoop.map ⟨Subtype.val, continuous_subtypeVal⟩ (coe_constContractibleLoop x)
      ((genLoopEquivOfUnique (Fin 1)).symm (sphereLoopPath β))) fun t ↦ by
        rw [GenLoop.map_apply, GenLoop.genLoopEquivOfUnique_symm_apply]
        exact coe_sphereLoopPath_apply β _
  have hmap : contractibleLoopsHomotopyGroupMulEquiv x
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (sphereLoopPath β)))) =
        ⟦GenLoop.map ⟨Subtype.val, continuous_subtypeVal⟩ (coe_constContractibleLoop x)
          ((genLoopEquivOfUnique (Fin 1)).symm (sphereLoopPath β))⟧ := by
    rw [contractibleLoopsHomotopyGroupMulEquiv_apply,
      HomotopyGroup.pi1MulEquivFundamentalGroup_symm_fromPath_mk, HomotopyGroup.map_mk]
  refine PeriodGroup.ext ?_ ?_ <;>
    simp only [SphericalPeriodGroup.area_ofContractibleLoopsHomotopyGroup,
      SphericalPeriodGroup.chern_ofContractibleLoopsHomotopyGroup,
      SphericalPeriodGroup.area_ofHomotopyGroup, SphericalPeriodGroup.chern_ofHomotopyGroup,
      toMul_ofMul, hmap, htorus]

/-- Gluing a sphere, the class of a double loop `β`, to a disc `p` moves the point of the cap
cover of `p` by the loop of contractible free loops traced by `β`, acting on the universal cover. -/
private theorem RawCap.toCapCover_vadd_mk (β : Ω (Ω X x) (Path.refl x))
    (p : Path γ (Path.refl x)) :
    RawCap.toCapCover ω c (Additive.ofMul (HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β))) +ᵥ
          FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)) =
      Quotient.mk'' (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (sphereLoopPath β)) •
        UniversalCover.mk
          ⟨γ.toCircle, toCircle_mem_contractibleLoops (Path.Homotopic.Quotient.mk p)⟩
          (Path.Homotopic.Quotient.mk
            (capCoverPath (toCircle_mem_contractibleLoops (Path.Homotopic.Quotient.mk p)) p))) := by
  have hvadd : Additive.ofMul (HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β))) +ᵥ
          FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p) =
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (p.trans β)) := by
    rw [RawCap.vadd_def, toMul_ofMul, MulEquiv.symm_apply_apply, FundamentalGroupoid.comp_eq,
      Path.Homotopic.Quotient.mk_trans]
  rw [hvadd, RawCap.toCapCover_mk, capCoverPath_trans, UniversalCover.smul_mk,
    FundamentalGroup.inv_def, Path.Homotopic.Quotient.mk_trans (sphereLoopPath β).symm,
    Path.Homotopic.Quotient.mk_symm]

/-- **Gluing a sphere of zero area and zero first Chern number to a disc does not move its point of
the cap cover**: the loop of contractible free loops traced by the sphere lies in the subgroup of
the cap cover. -/
private theorem RawCap.toCapCover_vadd_of_mem_ker {a : Additive (π_ 2 X x)}
    (ha : a ∈ (SphericalPeriodGroup.ofHomotopyGroup ω c x).ker) (D : RawCap γ) :
    (a +ᵥ D).toCapCover ω c = D.toCapCover ω c := by
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  obtain ⟨β, rfl⟩ := HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_fromPath_mk_surjective a
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective D
  rw [RawCap.toCapCover_vadd_mk, RawCap.toCapCover_mk]
  refine Quotient.sound ⟨⟨_, ?_⟩, rfl⟩
  rw [mem_capCoverSubgroup_iff, ofContractibleLoopsHomotopyGroup_sphereLoopPath,
    AddMonoidHom.mem_ker.1 ha]

namespace SphericalCapClass

variable (ω c) in
/-- **The point of the cap cover of a cap class.** Raw caps of `γ` with the same cap class differ
by a sphere of zero area and zero first Chern number, and gluing such a sphere does not move the
point of the cap cover. -/
def toCapCover (q : SphericalCapClass ω c γ) : CapCover ω c x :=
  Quotient.liftOn' q (RawCap.toCapCover ω c) fun D D' h ↦ by
    obtain ⟨k, rfl⟩ := h
    exact RawCap.toCapCover_vadd_of_mem_ker k.property D'

@[simp]
theorem toCapCover_mk (D : RawCap γ) : toCapCover ω c (mk ω c D) = D.toCapCover ω c := by
  rw [mk_def]
  rfl

/-- The point of the cap cover of a cap class of `γ` lies over `γ`. -/
@[simp]
theorem capCoverProj_toCapCover (q : SphericalCapClass ω c γ) :
    capCoverProj ω c x (toCapCover ω c q) = ⟨γ.toCircle, q.toCircle_mem_contractibleLoops⟩ :=
  induction_on q fun D ↦ by
    rw [toCapCover_mk]
    exact RawCap.capCoverProj_toCapCover D

end SphericalCapClass

variable [PathConnectedSpace X] [LocallyPathConnectedSpace (contractibleLoops X)]
  [SemilocallySimplyConnectedSpace (contractibleLoops X)]

/-- **Gluing a sphere to a disc moves its point of the cap cover by its class.** For a sphere
`a ∈ π₂(X, x)` and a raw cap `D`, the point of the cap cover of `a +ᵥ D` is that of `D` moved by
the class of `a` in the spherical period group. -/
theorem RawCap.toCapCover_vadd (a : Additive (π_ 2 X x)) (D : RawCap γ) :
    (a +ᵥ D).toCapCover ω c =
      SphericalPeriodGroup.ofHomotopyGroup ω c x a +ᵥ D.toCapCover ω c := by
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  obtain ⟨β, rfl⟩ := HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_fromPath_mk_surjective a
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective D
  rw [RawCap.toCapCover_vadd_mk, RawCap.toCapCover_mk,
    ← ofContractibleLoopsHomotopyGroup_sphereLoopPath, ofContractibleLoopsHomotopyGroup_vadd_mk,
    MulEquiv.apply_symm_apply]

namespace SphericalCapClass

/-- **Recapping moves the point of the cap cover by the period class.** -/
theorem toCapCover_vadd (g : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ) :
    toCapCover ω c (g +ᵥ q) = g +ᵥ toCapCover ω c q := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q using induction_on with
  | h D => rw [ofHomotopyGroup_vadd_mk, toCapCover_mk, toCapCover_mk, RawCap.toCapCover_vadd]

/-- The point of the cap cover of a cap class, as a point of the fibre over `γ`. -/
private def toCapCoverFiber [h : Nonempty (RawCap γ)] (q : SphericalCapClass ω c γ) :
    capCoverProj ω c x ⁻¹' {⟨γ.toCircle, h.elim RawCap.toCircle_mem_contractibleLoops⟩} :=
  ⟨toCapCover ω c q, capCoverProj_toCapCover q⟩

private theorem toCapCoverFiber_vadd [Nonempty (RawCap γ)] (g : SphericalPeriodGroup ω c)
    (q : SphericalCapClass ω c γ) : toCapCoverFiber (g +ᵥ q) = g +ᵥ toCapCoverFiber q :=
  Subtype.ext ((toCapCover_vadd g q).trans
    (CapCover.coe_vadd_fiber (x := x) _ (toCapCoverFiber q)).symm)

/-- Sending a cap class to its point of the fibre of the cap cover is a bijection: both are torsors
under the spherical period group, and the map is equivariant. -/
private theorem bijective_toCapCoverFiber [Nonempty (RawCap γ)] :
    Function.Bijective (toCapCoverFiber (ω := ω) (c := c) (γ := γ)) := by
  refine ⟨fun q q' h ↦ ?_, fun e ↦ ?_⟩
  · -- `q'` is `q` recapped by `q' -ᵥ q`, which therefore acts trivially on the fibre.
    have h' : (q' -ᵥ q) +ᵥ toCapCoverFiber q =
        (0 : SphericalPeriodGroup ω c) +ᵥ toCapCoverFiber q := by
      rw [← toCapCoverFiber_vadd, vsub_vadd, zero_vadd, h]
    exact (vsub_eq_zero_iff_eq.1 ((vadd_right_cancel_iff _).1 h')).symm
  · -- Recapping a cap class by the difference reaches any point of the fibre.
    obtain ⟨q₀⟩ : Nonempty (SphericalCapClass ω c γ) := inferInstance
    exact ⟨(e -ᵥ toCapCoverFiber q₀) +ᵥ q₀, by rw [toCapCoverFiber_vadd, vsub_vadd]⟩

variable (ω c) in
/-- **The fibre of the cap cover over a contractible loop at `x` is its set of cap classes.** For a
loop `γ` at `x` with a raw cap, sending a cap class to its point of the cap cover is a bijection
onto the fibre of the cap cover over `γ`. It intertwines the actions of the spherical period group
(`TauCeti.Floer.SphericalCapClass.capCoverFiberEquiv_vadd`). The raw cap makes `γ` a contractible
free loop (`TauCeti.Floer.RawCap.toCircle_mem_contractibleLoops`). -/
def capCoverFiberEquiv [h : Nonempty (RawCap γ)] :
    SphericalCapClass ω c γ ≃
      capCoverProj ω c x ⁻¹' {⟨γ.toCircle, h.elim RawCap.toCircle_mem_contractibleLoops⟩} :=
  Equiv.ofBijective toCapCoverFiber bijective_toCapCoverFiber

/-- The fibre equivalence sends a cap class to its point of the cap cover. -/
@[simp]
theorem coe_capCoverFiberEquiv_apply [Nonempty (RawCap γ)] (q : SphericalCapClass ω c γ) :
    (capCoverFiberEquiv ω c q : CapCover ω c x) = toCapCover ω c q := by
  rfl

/-- **The fibre equivalence intertwines recapping with the deck action**: recapping a cap class by
`g` moves its point of the cap cover by `g`. -/
theorem capCoverFiberEquiv_vadd [Nonempty (RawCap γ)] (g : SphericalPeriodGroup ω c)
    (q : SphericalCapClass ω c γ) :
    capCoverFiberEquiv ω c (g +ᵥ q) = g +ᵥ capCoverFiberEquiv ω c q :=
  toCapCoverFiber_vadd g q

end SphericalCapClass

end Fiber

end TauCeti.Floer
