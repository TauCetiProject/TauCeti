/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Isotopy
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding

/-!
# Group actions on local homology

Let a group `G` act on a Hausdorff space `M` modelled on a finite-dimensional real normed space
`E`, each `g : G` acting by a homeomorphism `z ↦ g • z`. For `g • x = y`, the element `g` induces
an isomorphism of local homology `Hₖ(M, M ∖ {x}) ≅ Hₖ(M, M ∖ {y})`
(`TauCeti.localHomologySMulIso`). Indexing the target by an arbitrary `y` with `g • x = y`, rather
than by `g • x` itself, lets an element of the stabilizer of `x` act on `Hₖ(M, M ∖ {x})` as an
endomorphism.

**The flat trivialization along an orbit.** Fix `x ∈ M` and let `π : G → M`, `g ↦ g • x`, be the
orbit map. When `G` is a topological space with continuous inversion acting continuously, for
instance a topological group, the isomorphisms induced by the elements of `G` are carried into
each other by the transport of local homology along the paths traced by `x`
(`TauCeti.localHomologySMulIso_hom_comp_localHomologyTransport`). Together they form a natural
isomorphism from the constant functor with value `Hₖ(M, M ∖ {x})` to the pullback along `π` of the
local homology system (`TauCeti.orbitLocalHomologyTrivialization`). In the dimension of `M`, with
integer coefficients, the local homology system is the orientation local system `or_M`, so this
trivializes `π^* or_M` on all of `G`, whether or not `M` is orientable: its value at `g` on a local
orientation `o` at `x` is the image `g_* o`.

**The isotropy orientation character.** An element `h` of the stabilizer of `x` acts on the
integral local homology `H_d(M, M ∖ {x}; ℤ) ≅ ℤ`, `d = dim M`, by multiplication by a sign
`χ(h) = ±1`, and `χ` is a character of the stabilizer (`TauCeti.isotropyOrientationCharacter`,
`TauCeti.localHomologySMulIso_hom_apply_eq_zsmul`). So `χ(h) = 1` exactly when `h` preserves the
local orientations at `x`. The trivialization above is equivariant up to `χ`:
`(g * h)_* o = χ(h) • g_* o` (`TauCeti.localHomologySMulIso_mul_hom_apply`). The character is
constant on the path components of the stabilizer
(`TauCeti.isotropyOrientationCharacter_eq_of_joined`), so it is trivial on a path-connected
stabilizer.

For a homogeneous space `M = G ⧸ H` with base point `x = eH`, the stabilizer is `H`. Barraud,
Damian, Humilière and Oancea use the trivialization of the orientation local system along
`G → G ⧸ H` and the sign of the isotropy action of `H` to state their Proposition 6.36 for
homogeneous spaces which need not be orientable; for a smooth action that sign is the sign of the
determinant of the isotropy representation on the tangent space at `x`, a comparison which is not
made here.

## Main definitions

* `TauCeti.localHomologySMulIso`: the isomorphism `Hₖ(M, M ∖ {x}) ≅ Hₖ(M, M ∖ {y})` induced by
  `g` with `g • x = y`.
* `TauCeti.orbitLocalHomologyTrivialization`: the flat trivialization of the pullback of the local
  homology system along an orbit map.
* `TauCeti.isotropyOrientationCharacter`: the character `χ : stabilizer G x →* ℤˣ`.

## Main results

* `TauCeti.localHomologySMulIso_hom_comp_localHomologyTransport_of_continuous`: the isomorphisms
  induced by a continuous family of elements of `G` are compatible with transport along the path
  of `x` under the family.
* `TauCeti.localHomologySMulIso_hom_comp_localHomologyTransport`: the isomorphisms induced by the
  elements of `G` are compatible with transport along the orbit.
* `TauCeti.localHomologySMulIso_hom_apply_eq_zsmul`: an element `h` of the stabilizer acts on
  `H_d(M, M ∖ {x}; ℤ)` as multiplication by `χ(h)`.
* `TauCeti.isotropyOrientationCharacter_eq_one_iff`: `χ(h) = 1` exactly when `h` acts trivially.
* `TauCeti.localHomologySMulIso_mul_hom_apply`: `(g * h)_* z = χ(h) • g_* z`.
* `TauCeti.isotropyOrientationCharacter_eq_of_joined`: `χ` is constant on path components of the
  stabilizer.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, local orientations and the orientation local
  system.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, Proposition 6.36.
-/

public section

noncomputable section

open CategoryTheory Limits Module MulAction

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {G : Type*} [Group G] {M : Type w} [TopologicalSpace M] [MulAction G M]

section SMulIso

variable [ContinuousConstSMul G M]

omit [TopologicalSpace M] [ContinuousConstSMul G M] in
/-- The map `z ↦ g • z` sends no point other than `x` to `g • x`. -/
private theorem preimage_smul_singleton_subset (g : G) {x y : M} (h : g • x = y) :
    (g • · : M → M) ⁻¹' {y} ⊆ {x} :=
  fun z hz ↦ (smul_left_cancel_iff g).1 ((hz : g • z = y).trans h.symm)

/-- The isomorphism `Hₖ(M, M ∖ {x}) ≅ Hₖ(M, M ∖ {y})` of local homology induced by the
homeomorphism `z ↦ g • z`, where `g • x = y`. -/
def localHomologySMulIso (g : G) {x y : M} (h : g • x = y) (k : ℕ) :
    localHomology R {x} k ≅ localHomology R {y} k where
  hom := localHomologyMap R ⟨(g • ·), continuous_const_smul g⟩
    (preimage_smul_singleton_subset g h) k
  inv := localHomologyMap R ⟨(g⁻¹ • ·), continuous_const_smul g⁻¹⟩
    (preimage_smul_singleton_subset g⁻¹ (inv_smul_eq_iff.2 h.symm)) k
  hom_inv_id := by
    rw [localHomologyMap_comp]
    exact localHomologyMap_eq_id R (inv_smul_smul g) _ k
  inv_hom_id := by
    rw [localHomologyMap_comp]
    exact localHomologyMap_eq_id R (smul_inv_smul g) _ k

/-- The isomorphism induced by `g` is the map of local homology induced by `z ↦ g • z`. -/
lemma localHomologySMulIso_hom (g : G) {x y : M} (h : g • x = y)
    (hpre : (g • · : M → M) ⁻¹' {y} ⊆ {x}) (k : ℕ) :
    (localHomologySMulIso R g h k).hom =
      localHomologyMap R ⟨(g • ·), continuous_const_smul g⟩ hpre k :=
  (rfl)

/-- The inverse of the isomorphism induced by `g` is the map of local homology induced by
`z ↦ g⁻¹ • z`. -/
lemma localHomologySMulIso_inv (g : G) {x y : M} (h : g • x = y)
    (hpre : (g⁻¹ • · : M → M) ⁻¹' {x} ⊆ {y}) (k : ℕ) :
    (localHomologySMulIso R g h k).inv =
      localHomologyMap R ⟨(g⁻¹ • ·), continuous_const_smul g⁻¹⟩ hpre k :=
  (rfl)

/-- The isomorphism induced by `g` is the map of local homology induced by `F (p, ·)`, for any
continuous family `F : P × M → M` of maps with `F (p, ·) = (g • ·)`. -/
lemma localHomologySMulIso_hom_eq_localHomologyMap {P : Type*} [TopologicalSpace P]
    {F : C(P × M, M)} {p : P} {g : G} (hF : ∀ z, F (p, z) = g • z) {x y : M} (h : g • x = y)
    (hpre : F.curry p ⁻¹' {y} ⊆ {x}) (k : ℕ) :
    (localHomologySMulIso R g h k).hom = localHomologyMap R (F.curry p) hpre k :=
  (localHomologySMulIso_hom R g h (preimage_smul_singleton_subset g h) k).trans
    (localHomologyMap_congr R (ContinuousMap.ext fun z ↦ (hF z).symm) _ k)

/-- The isomorphism induced by the identity is the identity. -/
@[simp]
lemma localHomologySMulIso_one {x : M} (h : (1 : G) • x = x) (k : ℕ) :
    localHomologySMulIso R (1 : G) h k = Iso.refl _ := by
  ext
  exact localHomologyMap_eq_id R (one_smul G) _ k

/-- The isomorphisms induced by a product are the composites. -/
@[reassoc (attr := simp)]
lemma localHomologySMulIso_hom_comp_localHomologySMulIso_hom (g g' : G) {x y z : M}
    (h : g • x = y) (h' : g' • y = z) (k : ℕ) :
    (localHomologySMulIso R g h k).hom ≫ (localHomologySMulIso R g' h' k).hom =
      (localHomologySMulIso R (g' * g) (by rw [mul_smul, h, h']) k).hom := by
  rw [localHomologySMulIso_hom R g h (preimage_smul_singleton_subset g h),
    localHomologySMulIso_hom R g' h' (preimage_smul_singleton_subset g' h'),
    localHomologySMulIso_hom R (g' * g) _
      (preimage_smul_singleton_subset _ (by rw [mul_smul, h, h'])),
    localHomologyMap_comp]
  exact localHomologyMap_congr R (ContinuousMap.ext fun w ↦ by simp [mul_smul]) _ k

/-- For `y = g • x` the isomorphism induced by `g` is the isomorphism of local homology induced by
the open embedding `z ↦ g • z`. -/
lemma localHomologySMulIso_eq_localHomologyIsoOfIsOpenEmbedding [T1Space M] (g : G) (x : M)
    (k : ℕ) :
    localHomologySMulIso R g (rfl : g • x = g • x) k =
      localHomologyIsoOfIsOpenEmbedding R (Homeomorph.smul g).isOpenEmbedding x k :=
  Iso.ext (localHomologyIsoOfIsOpenEmbedding_hom R _ x k).symm

end SMulIso

section Trivialization

variable [TopologicalSpace G] [ContinuousInv G] [ContinuousSMul G M] [T2Space M]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M]

/-- **The local homology isomorphisms of a group action are flat along continuous families.** Let
`ι : P → G` be a continuous family of elements of `G` and `π : P → M`, `π p = ι p • x`, the path
of `x` under it. For a path class `f : p ⟶ q` of `P`, the transport of local homology along
`π ∘ f` carries the isomorphism `Hₖ(M, M ∖ {x}) ≅ Hₖ(M, M ∖ {π p})` induced by `ι p` to the one
induced by `ι q`. -/
@[reassoc]
theorem localHomologySMulIso_hom_comp_localHomologyTransport_of_continuous {P : Type*}
    [TopologicalSpace P] (ι : C(P, G)) (x : M) {π : C(P, M)} (hπ : ∀ p, ι p • x = π p) (k : ℕ)
    {p q : FundamentalGroupoid P} (f : p ⟶ q) :
    (localHomologySMulIso R (ι p.as) (hπ p.as) k).hom ≫
        localHomologyTransport R M E k ((FundamentalGroupoid.map π).map f) =
      (localHomologySMulIso R (ι q.as) (hπ q.as) k).hom := by
  -- The isomorphisms are the maps induced by the family `F (p, y) = ι p • y`, which has the left
  -- inverses `(p, y) ↦ (ι p)⁻¹ • y`. Here `F (p, y)` is by definition `ι p • y`.
  let F : C(P × M, M) := ⟨fun r ↦ ι r.1 • r.2, by fun_prop⟩
  have hF (p : P) (y : M) :
      (⟨fun r ↦ (ι r.1)⁻¹ • r.2, by fun_prop⟩ : C(P × M, M)) (p, F (p, y)) = y :=
    inv_smul_smul (ι p) y
  rw [localHomologySMulIso_hom_eq_localHomologyMap R (F := F) (p := p.as) (fun _ ↦ rfl) _
      (preimage_curry_singleton_subset_of_leftInverse hF p.as (hπ p.as)),
    localHomologySMulIso_hom_eq_localHomologyMap R (F := F) (p := q.as) (fun _ ↦ rfl) _
      (preimage_curry_singleton_subset_of_leftInverse hF q.as (hπ q.as))]
  exact localHomologyMap_comp_localHomologyTransport_of_leftInverse R hF x hπ k f

/-- **The local homology isomorphisms of a group action are flat along orbits.** For an orbit map
`π : G → M`, `g ↦ g • x`, and a path class `f : g₀ ⟶ g₁` of `G`, the transport of local
homology along `π ∘ f` carries the isomorphism `Hₖ(M, M ∖ {x}) ≅ Hₖ(M, M ∖ {g₀ • x})` induced by
`g₀` to the one induced by `g₁`. -/
@[reassoc]
theorem localHomologySMulIso_hom_comp_localHomologyTransport (x : M) {π : C(G, M)}
    (hπ : ∀ g, g • x = π g) (k : ℕ) {g₀ g₁ : FundamentalGroupoid G} (f : g₀ ⟶ g₁) :
    (localHomologySMulIso R g₀.as (hπ g₀.as) k).hom ≫
        localHomologyTransport R M E k ((FundamentalGroupoid.map π).map f) =
      (localHomologySMulIso R g₁.as (hπ g₁.as) k).hom :=
  localHomologySMulIso_hom_comp_localHomologyTransport_of_continuous R (.id G) x hπ k f

/-- **The flat trivialization of local homology along an orbit.** For an orbit map
`π : G → M`, `g ↦ g • x`, the isomorphisms `Hₖ(M, M ∖ {x}) ≅ Hₖ(M, M ∖ {g • x})` induced by the
elements of `G` form a natural isomorphism from the constant functor to the pullback along `π` of
the local homology system. In the dimension of `M` and with integer coefficients, this
trivializes the pullback of the orientation local system along `π`. -/
def orbitLocalHomologyTrivialization (x : M) {π : C(G, M)} (hπ : ∀ g, g • x = π g) (k : ℕ) :
    (Functor.const (FundamentalGroupoid G)).obj (localHomology R {x} k) ≅
      FundamentalGroupoid.map π ⋙ localHomologySystem R M E k :=
  NatIso.ofComponents (fun g ↦ localHomologySMulIso R g.as (hπ g.as) k) fun f ↦
    (Category.id_comp _).trans
      (localHomologySMulIso_hom_comp_localHomologyTransport R x hπ k f).symm

@[simp]
lemma orbitLocalHomologyTrivialization_hom_app (x : M) {π : C(G, M)} (hπ : ∀ g, g • x = π g)
    (k : ℕ) (g : FundamentalGroupoid G) :
    (orbitLocalHomologyTrivialization (E := E) R x hπ k).hom.app g =
      (localHomologySMulIso R g.as (hπ g.as) k).hom :=
  (rfl)

@[simp]
lemma orbitLocalHomologyTrivialization_inv_app (x : M) {π : C(G, M)} (hπ : ∀ g, g • x = π g)
    (k : ℕ) (g : FundamentalGroupoid G) :
    (orbitLocalHomologyTrivialization (E := E) R x hπ k).inv.app g =
      (localHomologySMulIso R g.as (hπ g.as) k).inv :=
  (rfl)

end Trivialization

section Character

variable [ContinuousConstSMul G M] [T2Space M] {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}

/-- The integer by which an element of the stabilizer of `x` acts on `H_d(M, M ∖ {x}; ℤ)`. -/
private def stabilizerScalar (hd : finrank ℝ E = d) (x : M) (h : stabilizer G x) : ℤ :=
  (existsUnique_forall_localHomology_eq_zsmul hd ULift.moduleEquiv x
    (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) (mem_stabilizer_iff.1 h.2)
      d).hom.hom).choose

private lemma stabilizerScalar_spec (hd : finrank ℝ E = d) (x : M) (h : stabilizer G x)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) (mem_stabilizer_iff.1 h.2)
      d).hom z = stabilizerScalar hd x h • z :=
  (existsUnique_forall_localHomology_eq_zsmul hd ULift.moduleEquiv x _).choose_spec.1 z

/-- `stabilizerScalar hd x h` is the only integer by which `h` acts. -/
private lemma stabilizerScalar_eq (hd : finrank ℝ E = d) (x : M) (h : stabilizer G x) {c : ℤ}
    (hc : ∀ z, (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G)
      (mem_stabilizer_iff.1 h.2) d).hom z = c • z) :
    stabilizerScalar hd x h = c :=
  (existsUnique_forall_localHomology_eq_zsmul hd ULift.moduleEquiv x _).unique
    (stabilizerScalar_spec hd x h) hc

private lemma stabilizerScalar_one (hd : finrank ℝ E = d) (x : M) :
    stabilizerScalar hd x (1 : stabilizer G x) = 1 :=
  stabilizerScalar_eq hd x 1 fun z ↦ by simp

private lemma stabilizerScalar_mul (hd : finrank ℝ E = d) (x : M) (g h : stabilizer G x) :
    stabilizerScalar hd x (g * h) = stabilizerScalar hd x g * stabilizerScalar hd x h := by
  refine stabilizerScalar_eq hd x (g * h) fun z ↦ ?_
  -- The element `g * h` acts as `h` followed by `g`.
  simp only [Subgroup.coe_mul]
  rw [← localHomologySMulIso_hom_comp_localHomologySMulIso_hom _ (h : G) (g : G)
      (mem_stabilizer_iff.1 h.2) (mem_stabilizer_iff.1 g.2), ModuleCat.comp_apply,
    stabilizerScalar_spec hd x h, map_zsmul, stabilizerScalar_spec hd x g, smul_smul, mul_comm]

/-- **The isotropy orientation character.** An element `h` of the stabilizer of `x` acts on the
integral local homology `H_d(M, M ∖ {x}; ℤ) ≅ ℤ` in the dimension `d` of `M` by multiplication
by a sign `χ(h) = ±1` (`TauCeti.localHomologySMulIso_hom_apply_eq_zsmul`), and `χ(h) = 1` exactly
when `h` acts trivially (`TauCeti.isotropyOrientationCharacter_eq_one_iff`). -/
def isotropyOrientationCharacter (hd : finrank ℝ E = d) (x : M) : stabilizer G x →* ℤˣ :=
  MonoidHom.toHomUnits
    { toFun := stabilizerScalar hd x
      map_one' := stabilizerScalar_one hd x
      map_mul' := stabilizerScalar_mul hd x }

private lemma coe_isotropyOrientationCharacter (hd : finrank ℝ E = d) (x : M)
    (h : stabilizer G x) :
    (isotropyOrientationCharacter hd x h : ℤ) = stabilizerScalar hd x h :=
  MonoidHom.coe_toHomUnits _ _

/-- **An element of the stabilizer acts on top local homology by its orientation character.** -/
theorem localHomologySMulIso_hom_apply_eq_zsmul (hd : finrank ℝ E = d) {x : M}
    (h : stabilizer G x)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) (mem_stabilizer_iff.1 h.2)
      d).hom z = (isotropyOrientationCharacter hd x h : ℤ) • z := by
  rw [coe_isotropyOrientationCharacter]
  exact stabilizerScalar_spec hd x h z

/-- An element of the stabilizer has trivial orientation character exactly when it acts trivially
on `H_d(M, M ∖ {x}; ℤ)`, that is, when it preserves the local orientations at `x`. -/
theorem isotropyOrientationCharacter_eq_one_iff (hd : finrank ℝ E = d) {x : M}
    (h : stabilizer G x) :
    isotropyOrientationCharacter hd x h = 1 ↔
      ∀ z, (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G)
        (mem_stabilizer_iff.1 h.2) d).hom z = z := by
  refine ⟨fun h1 z ↦ by rw [localHomologySMulIso_hom_apply_eq_zsmul hd h, h1, Units.val_one,
    one_zsmul], fun hall ↦ Units.ext ?_⟩
  rw [coe_isotropyOrientationCharacter, Units.val_one]
  exact stabilizerScalar_eq hd x h fun z ↦ (hall z).trans (one_zsmul z).symm

/-- **The trivialization along the orbit is equivariant up to the orientation character.** For
`g` with `g • x = y` and `h` in the stabilizer of `x`, the image of a class `z` of
`H_d(M, M ∖ {x}; ℤ)` under `g * h` is `χ(h)` times its image under `g`. -/
theorem localHomologySMulIso_mul_hom_apply (hd : finrank ℝ E = d) {x y : M} (g : G)
    (hg : g • x = y) (h : stabilizer G x) (hgh : (g * h) • x = y)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (g * h) hgh d).hom z =
      (isotropyOrientationCharacter hd x h : ℤ) •
        (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) g hg d).hom z := by
  rw [← localHomologySMulIso_hom_comp_localHomologySMulIso_hom _ (h : G) g
    (mem_stabilizer_iff.1 h.2) hg, ModuleCat.comp_apply,
    localHomologySMulIso_hom_apply_eq_zsmul hd h, map_zsmul]

/-- **The orientation character is constant on path components of the stabilizer.** Elements of
the stabilizer of `x` joined by a path in the stabilizer act in the same way on local homology at
`x`. In particular `χ` is trivial on a path-connected stabilizer. -/
theorem isotropyOrientationCharacter_eq_of_joined [TopologicalSpace G] [ContinuousInv G]
    [ContinuousSMul G M] (hd : finrank ℝ E = d) {x : M} {h h' : stabilizer G x}
    (hJ : Joined h h') :
    isotropyOrientationCharacter hd x h = isotropyOrientationCharacter hd x h' := by
  -- The class of a path from `h` to `h'` in the stabilizer.
  set γ : FundamentalGroupoid.mk h ⟶ FundamentalGroupoid.mk h' :=
    Path.Homotopic.Quotient.mk hJ.somePath with hγ_def
  -- The point `x` stays put along `γ`: its image is the class of the constant path at `x`.
  have hγ : (FundamentalGroupoid.map (ContinuousMap.const (stabilizer G x) x)).map γ = 𝟙 _ := by
    rw [hγ_def, FundamentalGroupoid.map_map, ← Path.Homotopic.Quotient.mk_map,
      FundamentalGroupoid.id_eq_path_refl]
    refine congrArg _ (Path.ext ?_)
    ext t
    -- At each time both paths are at `x`: the mapped path is the constant map at its value.
    exact ContinuousMap.const_apply _ _
  -- So the transport along the image of `γ` is trivial.
  have hT : localHomologyTransport (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d
      ((FundamentalGroupoid.map (ContinuousMap.const (stabilizer G x) x)).map γ) = 𝟙 _ := by
    rw [hγ]
    exact localHomologyTransport_id _ M E d _
  -- So `h` and `h'` induce the same map, by flatness along the inclusion of the stabilizer.
  have hhh' : (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G)
      (mem_stabilizer_iff.1 h.2) d).hom =
        (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h' : G)
          (mem_stabilizer_iff.1 h'.2) d).hom := by
    have key := localHomologySMulIso_hom_comp_localHomologyTransport_of_continuous
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (E := E)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(stabilizer G x, G)) x
      (π := ContinuousMap.const (stabilizer G x) x) (fun g ↦ mem_stabilizer_iff.1 g.2) d γ
    -- `key` is stated at the points `π h = x` and `π h' = x` of the constant path `π`, and `hT`
    -- at the first of them; these are all `x` by definition, so they combine by `Eq.trans`.
    exact (Category.comp_id _).symm.trans ((congrArg _ hT.symm).trans key)
  refine Units.ext ?_
  rw [coe_isotropyOrientationCharacter, coe_isotropyOrientationCharacter]
  refine stabilizerScalar_eq hd x h fun z ↦ ?_
  rw [hhh']
  exact localHomologySMulIso_hom_apply_eq_zsmul hd h' z

end Character

end TauCeti
