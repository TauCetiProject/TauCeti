/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Exponent
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The exponent of an abelian group kills the homology of `K(A, 1)`

Let `k` be a hereditary commutative ring, expressed by requiring every `k`-module to have
projective dimension at most one, for instance `ℤ` or a field. For a commutative group `G`, the
exponent of `G` kills the group homology `Hₙ₊₁(G, k)` with trivial coefficients
(`groupHomology.exponent_nsmul_trivial_eq_zero`), and hence the singular homology
`Hₙ₊₁(BG; k)` of Milnor's classifying space
(`TauCeti.exponent_nsmul_classifyingSpace_singularHomology_eq_zero`). The bound depends neither on
the rank nor on the cardinality of `G`, so it also holds for infinite groups of finite exponent.

The proof has three steps.

* **Products.** If a number `e` kills the positive-degree homology of `BG` and of `BH`, it kills
  that of `B(G × H)` (`TauCeti.nsmul_classifyingSpace_prod_singularHomology_eq_zero`). The
  comparison map `B(G × H) ⟶ BG × BH` is a homology isomorphism, and over a hereditary ring the
  Künneth sequence of `BG × BH` splits, so `e` kills it
  (`TopCat.nsmul_singularHomology_tensor_eq_zero`). Without the splitting the extension would
  only give `e²`, a bound that would grow with the number of factors.
* **Finite groups.** A finite commutative group is a product of finitely many cyclic groups
  (`CommGroup.equiv_prod_multiplicative_zmod_of_finite`), whose orders divide the exponent, and
  the order of a finite group kills the positive-degree homology of its classifying space
  (`TauCeti.natCard_nsmul_classifyingSpace_singularHomology_eq_zero`).
* **Arbitrary groups.** A commutative group of positive exponent is torsion, hence locally finite,
  so every homology class comes from a finite subgroup
  (`groupHomology.exists_finite_subgroup_map_eq`), whose exponent divides that of `G`.

For an abelian group `A`, the classifying space `B(Multiplicative A)` is an Eilenberg--MacLane space
`K(A, 1)`. Serre's axiom on the homology of `K(A, 1)` for the class
`AddCommGrpCat.isKilledBySomePower d` of groups annihilated by some power of `d` asks that this
class contain `Hₙ₊₁(K(A, 1))` whenever it contains `A`. It follows, by the same power of `d`,
for every `A` (`TauCeti.isKilledBySomePower_classifyingSpace_singularHomology`), with no finiteness
assumption on `A`.

## Main results

* `groupHomology.exponent_nsmul_trivial_eq_zero`: the exponent of a commutative group `G` kills
  `Hₙ₊₁(G, k)`.
* `TauCeti.exponent_nsmul_classifyingSpace_singularHomology_eq_zero`: the exponent of a commutative
  group `G` kills `Hₙ₊₁(BG; k)`.
* `TauCeti.isKilledBySomePower_classifyingSpace_singularHomology`: Serre's `K(A, 1)` axiom for the
  groups annihilated by some power of `d`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.B, the Künneth
  formula.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, Section 10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

/-- A number killing the positive-degree homology of `BG` kills that of `BH`, for `G ≃* H`. -/
private lemma nsmul_classifyingSpace_singularHomology_eq_zero_of_mulEquiv {G H : Type u}
    [Group G] [Group H] (φ : G ≃* H) {e : ℕ}
    (hG : ∀ n (x : ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)),
      e • x = 0)
    (n : ℕ) (x : ((singularChains k).obj (TopCat.of (classifyingSpace H))).homology (n + 1)) :
    e • x = 0 := by
  let f := (singularChains k).map (TopCat.ofHom φ.toMonoidHom.classifyingSpaceMap)
  let g := (singularChains k).map (TopCat.ofHom φ.symm.toMonoidHom.classifyingSpaceMap)
  have hφ : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id H := by ext; simp
  have hgf : g ≫ f = 𝟙 _ := by
    rw [← Functor.map_comp, ← TopCat.ofHom_comp, ← MonoidHom.classifyingSpaceMap_comp, hφ,
      MonoidHom.classifyingSpaceMap_id]
    exact (singularChains k).map_id _
  have hx : x = (HomologicalComplex.homologyMap f (n + 1)).hom
      ((HomologicalComplex.homologyMap g (n + 1)).hom x) := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, hgf,
      HomologicalComplex.homologyMap_id]
    rfl
  rw [hx, ← map_nsmul, hG, map_zero]

section Hereditary

variable [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1]

/-- A number killing the positive-degree homology of the classifying spaces of finitely many
groups kills that of their product. -/
private lemma nsmul_classifyingSpace_pi_singularHomology_eq_zero (ι : Type) [Finite ι]
    (G : ι → Type u) [∀ i, Group (G i)] {e : ℕ}
    (hG : ∀ i n (x : ((singularChains k).obj (TopCat.of (classifyingSpace (G i)))).homology
      (n + 1)), e • x = 0)
    (n : ℕ) (x : ((singularChains k).obj (TopCat.of (classifyingSpace (∀ i, G i)))).homology
      (n + 1)) :
    e • x = 0 := by
  have := Fintype.ofFinite ι
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ (G : ι → Type u) [∀ i, Group (G i)],
      (∀ i n (x : ((singularChains k).obj (TopCat.of (classifyingSpace (G i)))).homology (n + 1)),
        e • x = 0) →
      ∀ n (x : ((singularChains k).obj (TopCat.of (classifyingSpace (∀ i, G i)))).homology
        (n + 1)), e • x = 0) ?_ ?_ ?_ ι G hG n x
  · -- reindexing along an equivalence of index types
    intro α β _ eqv h G _ hG
    exact nsmul_classifyingSpace_singularHomology_eq_zero_of_mulEquiv k
      ({ Equiv.piCongrLeft' G eqv.symm with map_mul' := fun _ _ ↦ rfl } :
        (∀ b, G b) ≃* ∀ a, G (eqv a)).symm
      (h (fun a ↦ G (eqv a)) fun a ↦ hG (eqv a))
  · -- the empty product is the trivial group
    intro G _ _ n x
    have hx := natCard_nsmul_classifyingSpace_singularHomology_eq_zero k x
    rw [Nat.card_unique, one_smul] at hx
    rw [hx, smul_zero]
  · -- split off the factor indexed by `none`
    intro α _ h G _ hG
    exact nsmul_classifyingSpace_singularHomology_eq_zero_of_mulEquiv k
      ({ Equiv.piOptionEquivProd with map_mul' := fun _ _ ↦ rfl } :
        (∀ i, G i) ≃* G none × ∀ a, G (some a)).symm
      (nsmul_classifyingSpace_prod_singularHomology_eq_zero _ _ k (hG none)
        (h (fun a ↦ G (some a)) fun a ↦ hG (some a)))

/-- If `gᵉ = 1` for every element of a finite commutative group `G`, then `e` kills the
positive-degree homology of `BG`: `G` is a finite product of cyclic groups, whose orders divide
`e`. -/
private lemma nsmul_classifyingSpace_singularHomology_eq_zero_of_finite {G : Type u} [CommGroup G]
    [Finite G] {e : ℕ} (he : ∀ g : G, g ^ e = 1) (n : ℕ)
    (x : ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :
    e • x = 0 := by
  classical
  obtain ⟨ι, _, m, hm, ⟨φ⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let ψ : G ≃* ∀ i, ULift.{u} (Multiplicative (ZMod (m i))) :=
    φ.trans (MulEquiv.piCongrRight fun _ ↦ MulEquiv.ulift.symm)
  refine nsmul_classifyingSpace_singularHomology_eq_zero_of_mulEquiv k ψ.symm
    (nsmul_classifyingSpace_pi_singularHomology_eq_zero k ι _ fun i p y ↦ ?_) n x
  have : NeZero (m i) := ⟨by have := hm i; omega⟩
  -- the order `m i` of the cyclic factor divides `e`
  obtain ⟨c, hc⟩ : m i ∣ e := by
    let u : ULift.{u} (Multiplicative (ZMod (m i))) := ⟨Multiplicative.ofAdd 1⟩
    have h₁ : (Pi.mulSingle i u : ∀ i, ULift.{u} (Multiplicative (ZMod (m i)))) ^ e = 1 := by
      have := he (ψ.symm (Pi.mulSingle i u))
      rwa [← map_pow, MulEquiv.symm_apply_eq, map_one] at this
    have h₂ : u ^ e = 1 := by
      simpa using congr_fun h₁ i
    have h₃ : ((e : ℕ) : ZMod (m i)) = 0 := by
      simpa [u] using congr(Multiplicative.toAdd (ULift.down $h₂))
    exact (ZMod.natCast_eq_zero_iff e (m i)).1 h₃
  have hy := natCard_nsmul_classifyingSpace_singularHomology_eq_zero k y
  rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hy
  rw [hc, mul_nsmul, hy, smul_zero]

end Hereditary

end TauCeti

namespace groupHomology

variable (k : Type u) [CommRing k] [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1]

/-- **The exponent of an abelian group kills its positive-degree homology.** Over a hereditary
commutative ring `k`, for instance `ℤ`, the exponent of a commutative group `G` kills the group
homology `Hₙ₊₁(G, k)` with trivial coefficients. The bound depends neither on the rank nor on the
cardinality of `G`. -/
theorem exponent_nsmul_trivial_eq_zero (G : Type u) [CommGroup G] {n : ℕ}
    (x : groupHomology (Rep.trivial k G k) (n + 1)) : Monoid.exponent G • x = 0 := by
  rcases eq_or_ne (Monoid.exponent G) 0 with h | h
  · rw [h, zero_smul]
  -- A group of positive exponent is torsion, hence locally finite, and every class comes from a
  -- finite subgroup, whose elements also satisfy `gᵉ = 1` for the exponent `e` of `G`.
  have := TauCeti.Group.isLocallyFinite_iff_isMulTorsion.2 fun g : G ↦
    isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero h, Monoid.pow_exponent_eq_one g⟩
  obtain ⟨S, _, y, rfl⟩ := groupHomology.exists_finite_subgroup_map_eq x
  have hS : ∀ z : groupHomology (Rep.trivial k S k) (n + 1), Monoid.exponent G • z = 0 := by
    intro z
    let f := (TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology k S (n + 1)).toLinearEquiv
    apply f.symm.injective
    rw [map_nsmul, map_zero]
    exact TauCeti.nsmul_classifyingSpace_singularHomology_eq_zero_of_finite k
      (fun s ↦ Subtype.ext (Monoid.pow_exponent_eq_one (s : G))) n _
  -- the restriction of the trivial representation to `S` is by definition the trivial one
  have hy : Monoid.exponent G • y = 0 := hS y
  rw [← map_nsmul, hy, map_zero]

end groupHomology

namespace TauCeti

variable (k : Type u) [CommRing k]

section Hereditary

variable [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1]

/-- **The exponent of an abelian group kills the homology of its classifying space.** Over a
hereditary commutative ring `k`, for instance `ℤ`, the exponent of a commutative group `G` kills
`Hₙ₊₁(BG; k)`. -/
theorem exponent_nsmul_classifyingSpace_singularHomology_eq_zero (G : Type u) [CommGroup G]
    {n : ℕ} (x : ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :
    Monoid.exponent G • x = 0 := by
  apply (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv.injective
  rw [map_nsmul, map_zero]
  exact groupHomology.exponent_nsmul_trivial_eq_zero k G _

/-- **Serre's `K(A, 1)` axiom for the groups annihilated by a power of `d`.** Over a hereditary
commutative ring `k`, for instance `ℤ`, if an abelian group `A` is annihilated by some power of
`d`, then so is the positive-degree homology of the Eilenberg--MacLane space
`K(A, 1) = B(Multiplicative A)`, by the same power. -/
theorem isKilledBySomePower_classifyingSpace_singularHomology {d : ℕ} {A : AddCommGrpCat.{u}}
    (hA : AddCommGrpCat.isKilledBySomePower d A) (n : ℕ) :
    AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of
      (((singularChains k).obj (TopCat.of (classifyingSpace (Multiplicative A)))).homology
        (n + 1))) := by
  obtain ⟨m, hm⟩ := (AddCommGrpCat.prop_isKilledBySomePower_iff d A).1 hA
  obtain ⟨c, hc⟩ : Monoid.exponent (Multiplicative A) ∣ d ^ m :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a ↦ by
      have ha := hm a.toAdd
      rw [← Nat.cast_pow, natCast_zsmul] at ha
      simpa using congr(Multiplicative.ofAdd $ha)
  refine (AddCommGrpCat.prop_isKilledBySomePower_iff d _).2 ⟨m, fun x ↦ ?_⟩
  rw [← Nat.cast_pow, natCast_zsmul, hc, mul_nsmul,
    exponent_nsmul_classifyingSpace_singularHomology_eq_zero, smul_zero]

end Hereditary

end TauCeti
