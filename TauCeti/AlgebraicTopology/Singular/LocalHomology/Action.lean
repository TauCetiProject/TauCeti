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

omit [MulAction G M] [ContinuousConstSMul G M] in
/-- A continuous map which is pointwise the identity induces the identity of local homology. -/
private lemma localHomologyMap_eq_id {S : Set M} {j : C(M, M)} (hj : ∀ z, j z = z)
    (h : j ⁻¹' S ⊆ S) (k : ℕ) : localHomologyMap R j h k = 𝟙 _ := by
  obtain rfl : j = ContinuousMap.id M := ContinuousMap.ext hj
  rw [localHomologyMap_id]
  exact localHomologyRestriction_refl R S k

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
  localHomologyMap_comp_localHomologyTransport_of_leftInverse R
    (F := ⟨fun q : G × M ↦ q.1 • q.2, continuous_smul⟩)
    (F' := ⟨fun q : G × M ↦ q.1⁻¹ • q.2, by fun_prop⟩) (fun g y ↦ inv_smul_smul g y) x hπ k f

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

omit [MulAction G M] [ContinuousConstSMul G M] in
/-- Every additive endomorphism of `H_d(M, M ∖ {x}; ℤ) ≅ ℤ` in the dimension `d` of `M` is
multiplication by a unique integer. -/
private lemma existsUnique_forall_eq_smul (hd : finrank ℝ E = d) (x : M)
    (φ : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d →+
      localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    ∃! c : ℤ, ∀ z, φ z = c • z := by
  let e := (localHomologySingletonLinearEquiv (ModuleCat.of ℤ (ULift.{w} ℤ)) hd ULift.moduleEquiv
    x).toAddEquiv
  -- Every class is a multiple of the generator `u = e⁻¹ 1`.
  have he (z) : z = e z • e.symm 1 :=
    e.injective (by rw [map_zsmul, e.apply_symm_apply, zsmul_eq_mul, mul_one, Int.cast_id])
  refine ⟨e (φ (e.symm 1)), fun z ↦ ?_, fun c hc ↦ ?_⟩
  · conv_lhs => rw [he z, map_zsmul, he (φ (e.symm 1)), smul_smul, mul_comm, ← smul_smul, ← he z]
  · rw [hc, map_zsmul, e.apply_symm_apply, zsmul_eq_mul, mul_one, Int.cast_id]

/-- The action of an element of the stabilizer of `x` on `H_d(M, M ∖ {x}; ℤ)`. -/
private def stabilizerAddHom (x : M) (d : ℕ) (h : stabilizer G x) :
    localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d →+
      localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d :=
  (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) (mem_stabilizer_iff.1 h.2)
    d).hom.hom.toAddMonoidHom

/-- The integer by which an element of the stabilizer of `x` acts on `H_d(M, M ∖ {x}; ℤ)`. -/
private def stabilizerScalar (hd : finrank ℝ E = d) (x : M) (h : stabilizer G x) : ℤ :=
  (existsUnique_forall_eq_smul hd x (stabilizerAddHom x d h)).choose

private lemma stabilizerScalar_spec (hd : finrank ℝ E = d) (x : M) (h : stabilizer G x)
    (hh : (h : G) • x = x)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) hh d).hom z =
      stabilizerScalar hd x h • z :=
  (existsUnique_forall_eq_smul hd x (stabilizerAddHom x d h)).choose_spec.1 z

private lemma stabilizerScalar_one (hd : finrank ℝ E = d) (x : M) :
    stabilizerScalar hd x (1 : stabilizer G x) = 1 := by
  refine (existsUnique_forall_eq_smul hd x (stabilizerAddHom x d 1)).unique
    (stabilizerScalar_spec hd x 1 (one_smul G x)) fun z ↦ ?_
  have h1 : (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ))
      ((1 : stabilizer G x) : G) (one_smul G x) d).hom = 𝟙 _ :=
    localHomologyMap_eq_id _ (one_smul G) _ d
  exact (congrArg (fun f ↦ ModuleCat.Hom.hom f z) h1).trans (one_zsmul z).symm

private lemma stabilizerScalar_mul (hd : finrank ℝ E = d) (x : M) (g h : stabilizer G x) :
    stabilizerScalar hd x (g * h) = stabilizerScalar hd x g * stabilizerScalar hd x h := by
  refine (existsUnique_forall_eq_smul hd x (stabilizerAddHom x d (g * h))).unique
    (stabilizerScalar_spec hd x (g * h) (mem_stabilizer_iff.1 (g * h).2)) fun z ↦ ?_
  -- The element `g * h` acts as `h` followed by `g`.
  have hcomp := localHomologySMulIso_hom_comp_localHomologySMulIso_hom
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) (g : G) (mem_stabilizer_iff.1 h.2)
    (mem_stabilizer_iff.1 g.2) d
  calc _ = (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (g : G)
        (mem_stabilizer_iff.1 g.2) d).hom
          ((localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G)
            (mem_stabilizer_iff.1 h.2) d).hom z) := by
        rw [← ModuleCat.comp_apply, hcomp]
        rfl
    _ = _ := by
      rw [stabilizerScalar_spec hd x h, map_zsmul, stabilizerScalar_spec hd x g, smul_smul,
        mul_comm]

/-- **The isotropy orientation character.** An element `h` of the stabilizer of `x` acts on the
integral local homology `H_d(M, M ∖ {x}; ℤ) ≅ ℤ` in the dimension `d` of `M` by multiplication
by a sign `χ(h) = ±1` (`TauCeti.localHomologySMulIso_hom_apply_eq_zsmul`), and `χ(h) = 1` exactly
when `h` acts trivially (`TauCeti.isotropyOrientationCharacter_eq_one_iff`). -/
def isotropyOrientationCharacter (hd : finrank ℝ E = d) (x : M) : stabilizer G x →* ℤˣ :=
  MonoidHom.toHomUnits
    { toFun := stabilizerScalar hd x
      map_one' := stabilizerScalar_one hd x
      map_mul' := stabilizerScalar_mul hd x }

/-- **An element of the stabilizer acts on top local homology by its orientation character.** -/
theorem localHomologySMulIso_hom_apply_eq_zsmul (hd : finrank ℝ E = d) {x : M}
    (h : stabilizer G x) (hh : (h : G) • x = x)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) hh d).hom z =
      (isotropyOrientationCharacter hd x h : ℤ) • z :=
  stabilizerScalar_spec hd x h hh z

/-- An element of the stabilizer has trivial orientation character exactly when it acts trivially
on `H_d(M, M ∖ {x}; ℤ)`, that is, when it preserves the local orientations at `x`. -/
theorem isotropyOrientationCharacter_eq_one_iff (hd : finrank ℝ E = d) {x : M}
    (h : stabilizer G x) (hh : (h : G) • x = x) :
    isotropyOrientationCharacter hd x h = 1 ↔
      ∀ z, (localHomologySMulIso (ModuleCat.of ℤ (ULift.{w} ℤ)) (h : G) hh d).hom z = z := by
  refine ⟨fun h1 z ↦ by rw [localHomologySMulIso_hom_apply_eq_zsmul hd h, h1, Units.val_one,
    one_zsmul], fun hall ↦ Units.ext ?_⟩
  exact (existsUnique_forall_eq_smul hd x (stabilizerAddHom x d h)).unique
    (stabilizerScalar_spec hd x h hh) fun z ↦ (hall z).trans (one_zsmul z).symm

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
  -- The family `(h, y) ↦ h • y` over the stabilizer fixes `x`, so the transport is trivial.
  have key := localHomologyMap_comp_localHomologyTransport_of_leftInverse
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (E := E)
    (F := ⟨fun q : stabilizer G x × M ↦ (q.1 : G) • q.2, by fun_prop⟩)
    (F' := ⟨fun q : stabilizer G x × M ↦ (q.1 : G)⁻¹ • q.2, by fun_prop⟩)
    (fun g y ↦ inv_smul_smul (g : G) y) x (o := ContinuousMap.const _ x)
    (fun g ↦ mem_stabilizer_iff.1 g.2) d
    (Path.Homotopic.Quotient.mk hJ.somePath :
      FundamentalGroupoid.mk h ⟶ FundamentalGroupoid.mk h')
  have hconst : (FundamentalGroupoid.map (ContinuousMap.const (stabilizer G x) x)).map
      (Path.Homotopic.Quotient.mk hJ.somePath :
        FundamentalGroupoid.mk h ⟶ FundamentalGroupoid.mk h') =
        𝟙 ((FundamentalGroupoid.map (ContinuousMap.const (stabilizer G x) x)).obj
          (FundamentalGroupoid.mk h)) :=
    congrArg Path.Homotopic.Quotient.mk (Path.ext rfl)
  have hT : localHomologyTransport (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d
      ((FundamentalGroupoid.map (ContinuousMap.const (stabilizer G x) x)).map
        (Path.Homotopic.Quotient.mk hJ.somePath :
          FundamentalGroupoid.mk h ⟶ FundamentalGroupoid.mk h')) = 𝟙 _ := by
    rw [hconst]
    exact localHomologyTransport_id _ M E d _
  refine Units.ext ((existsUnique_forall_eq_smul hd x (stabilizerAddHom x d h)).unique
    (stabilizerScalar_spec hd x h (mem_stabilizer_iff.1 h.2)) fun z ↦ ?_)
  exact (congrArg (fun φ ↦ ModuleCat.Hom.hom φ z)
    (((Category.comp_id _).symm.trans (congrArg _ hT.symm)).trans key)).trans
      (stabilizerScalar_spec hd x h' (mem_stabilizer_iff.1 h'.2) z)

end Character

end TauCeti
