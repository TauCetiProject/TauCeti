/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.Doubling.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.SesquilinearForm.Doubling.Graph
import TauCeti.LinearAlgebra.SesquilinearForm.Rank

/-!
# Links of isometries on an isotropic reduction

For an isotropic subspace `A`, a realization of `Aᗮ/A` in a space `X` sends the graph of an
isometry to a linear relation on `X`: retain exactly the pairs whose entries both lie in `Aᗮ`,
then take their classes. This preserves the dimension required of an isometry graph even when
the relation on `X` is not the graph of a map. For a middle form with a negative summand,
exchanging the negative coordinates between the two copies turns this relation into an
isotropic subspace for the double of the corresponding positive form.

This construction and coordinate exchange are used for Bessel links in lsernau/grh-lean,
revision `72fead1`, `grh/src/New/Spanning/Unfolding/Link.lean` (`New.Filling.linkIsometry`).
-/

public section

open Module Submodule

namespace LinearMap

variable {K V X : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X] [Module K X]
  {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {A : Submodule K V}

/-- The map sending a vector in both orthogonal complements to the two reduced coordinates. -/
private def isometryLinkMap (r : A.orthogonalBilin B →ₗ[K] X) (g : V ≃ₗ[K] V) :
    (A.orthogonalBilin B ⊓ (A.orthogonalBilin B).comap g.toLinearMap : Submodule K V) →ₗ[K]
      X × X :=
  (r.comp (inclusion inf_le_left)).prod
    (r.comp ((g.toLinearMap.domRestrict _).codRestrict _ fun x ↦ x.property.2))

/-- The reduced relation of `g`: project both entries of its graph via `r`, retaining only
pairs with both entries in the orthogonal complement of `A`. When `r` realizes `Aᗮ/A`, this is
the link of `g` on that quotient. -/
def isometryLink (B : V →ₛₗ[σ] V →ₗ[K] K) (A : Submodule K V)
    (r : A.orthogonalBilin B →ₗ[K] X) (g : V ≃ₗ[K] V) : Submodule K (X × X) :=
  LinearMap.range (isometryLinkMap r g)

/-- A pair lies in the reduced relation exactly when it lifts to a pair in the graph of `g` with
both entries in `Aᗮ`. -/
theorem mem_isometryLink_iff (B : V →ₛₗ[σ] V →ₗ[K] K) (A : Submodule K V)
    (r : A.orthogonalBilin B →ₗ[K] X) (g : V ≃ₗ[K] V) {z : X × X} :
    z ∈ B.isometryLink A r g ↔ ∃ x y : A.orthogonalBilin B, g (x : V) = y ∧ (r x, r y) = z := by
  rw [isometryLink, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, x.property.1⟩, ⟨g x, x.property.2⟩, rfl, hx⟩
  · rintro ⟨x, y, hxy, rfl⟩
    have hy : g (x : V) ∈ A.orthogonalBilin B := hxy.symm ▸ y.property
    refine ⟨⟨x, x.property, hy⟩, Prod.ext rfl ?_⟩
    exact congrArg r (Subtype.ext hxy)

/-- Composing on either side by an automorphism that preserves the orthogonal complement
and acts trivially after reduction does not change the link. -/
theorem isometryLink_trans_eq (B : V →ₛₗ[σ] V →ₗ[K] K) (r : A.orthogonalBilin B →ₗ[K] X)
    (g a b : V ≃ₗ[K] V)
    (ha : ∀ x, a x ∈ A.orthogonalBilin B ↔ x ∈ A.orthogonalBilin B)
    (hb : ∀ x, b x ∈ A.orthogonalBilin B ↔ x ∈ A.orthogonalBilin B)
    (hra : ∀ x y : A.orthogonalBilin B, a (x : V) = y → r x = r y)
    (hrb : ∀ x y : A.orthogonalBilin B, b (x : V) = y → r x = r y) :
    B.isometryLink A r (a.trans (g.trans b)) = B.isometryLink A r g := by
  ext z
  simp only [mem_isometryLink_iff, LinearEquiv.trans_apply]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    let x' : A.orthogonalBilin B := ⟨a x, (ha x).2 x.property⟩
    let y' : A.orthogonalBilin B := ⟨g (a x), (hb _).1 (hxy.symm ▸ y.property)⟩
    exact ⟨x', y', rfl, Prod.ext (hra x x' rfl).symm (hrb y' y hxy)⟩
  · rintro ⟨x, y, hxy, rfl⟩
    have hx : a (a.symm (x : V)) = x := a.apply_symm_apply x
    let x' : A.orthogonalBilin B := ⟨a.symm x, (ha _).1 (hx.symm ▸ x.property)⟩
    let y' : A.orthogonalBilin B := ⟨b y, (hb y).2 y.property⟩
    exact ⟨x', y', by rw [hx, hxy], Prod.ext (hra x' x hx) (hrb y y' rfl).symm⟩

/-- A form-preserving reduction takes the graph of an isometry to an isotropic relation. -/
theorem isometryLink_le_orthogonalBilin_doubled (B : V →ₛₗ[σ] V →ₗ[K] K)
    (r : A.orthogonalBilin B →ₗ[K] X) (g : B.isometryGroup) {C : X →ₛₗ[σ] X →ₗ[K] K}
    (hr : ∀ x y : A.orthogonalBilin B, C (r x) (r y) = B x y) :
    B.isometryLink A r g.val ≤ (B.isometryLink A r g.val).orthogonalBilin C.doubled := by
  intro z hz w hw
  obtain ⟨x, y, hxy, rfl⟩ := (B.mem_isometryLink_iff A r g.val).1 hz
  obtain ⟨u, v, huv, rfl⟩ := (B.mem_isometryLink_iff A r g.val).1 hw
  simp only [doubled_apply, hr u x, hr v y, ← hxy, ← huv, B.isometryGroup_map_app, sub_self]

/-- Reduction by an isotropic subspace takes an isometry graph to a relation of half the
ambient dimension. The two occurrences of the intersection of the original isotropic
subspace with its translate cancel in rank-nullity. -/
theorem finrank_isometryLink [FiniteDimensional K V] {τ : K ≃+* K}
    (B : V →ₛₗ[τ.toRingHom] V →ₗ[K] K) {A : Submodule K V}
    (r : A.orthogonalBilin B →ₗ[K] X) (g : B.isometryGroup)
    (hB : B.SeparatingLeft) (hA : A ≤ A.orthogonalBilin B) (hr : Function.Surjective r)
    (hker : r.ker = A.comap (A.orthogonalBilin B).subtype) :
    finrank K (B.isometryLink A r g.val) = finrank K X := by
  let D := A.orthogonalBilin B ⊓ (A.orthogonalBilin B).comap g.val.toLinearMap
  let E := A ⊓ A.comap g.val.toLinearMap
  -- The source is the orthogonal of a sum; the kernel is the corresponding intersection.
  have hED : E ≤ D := inf_le_inf hA (Submodule.comap_mono hA)
  have hD : D = (A ⊔ A.comap g.val.toLinearMap).orthogonalBilin B := by
    rw [orthogonalBilin_sup]
    refine congrArg (A.orthogonalBilin B ⊓ ·) ?_
    ext x
    simp only [mem_comap, LinearEquiv.coe_coe, mem_orthogonalBilin]
    refine ⟨fun hx y hy ↦ ?_, fun hx y hy ↦ ?_⟩
    · simpa only [B.isometryGroup_map_app g y x] using hx (g.val y) hy
    · have he := hx (g.val.symm y) (by simpa using hy)
      simpa only [← B.isometryGroup_map_app g (g.val.symm y) x, LinearEquiv.apply_symm_apply]
        using he
  have hk : (isometryLinkMap r g.val).ker = E.comap D.subtype := by
    rw [isometryLinkMap, LinearMap.ker_prod, LinearMap.ker_comp, LinearMap.ker_comp, hker]
    ext z
    simp only [mem_inf, mem_comap, coe_subtype, inclusion_apply, E]
    rfl
  have hke := (Submodule.comapSubtypeEquivOfLe hED).finrank_eq
  have ha := A.finrank_add_finrank_orthogonalBilin hB
  have hd := (A ⊔ A.comap g.val.toLinearMap).finrank_add_finrank_orthogonalBilin hB
  have he := A.finrank_sup_add_finrank_inf_eq (A.comap g.val.toLinearMap)
  have hc : finrank K (A.comap g.val.toLinearMap) = finrank K A := by
    rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hz := r.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hr, finrank_top, hker,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at hz
  have hl := (isometryLinkMap r g.val).finrank_range_add_finrank_ker
  rw [hk, hke, ← isometryLink] at hl
  rw [← hD] at hd
  rw [hc] at he
  dsimp only [D, E] at hd hl
  omega

/-- When the middle form is the difference of two forms with anisotropic sum, exchange the
second coordinates of the two reduced vectors. The resulting relation is the graph of a unique
isometry for the sum. In a Bessel link the exchanged summand is the negative line. -/
theorem existsUnique_isometry_of_isometryLink [FiniteDimensional K V] {τ : K ≃+* K}
    (B : V →ₛₗ[τ.toRingHom] V →ₗ[K] K) {A : Submodule K V}
    {P N : Type*} [AddCommGroup P] [Module K P] [AddCommGroup N] [Module K N]
    (r : A.orthogonalBilin B →ₗ[K] (P × N)) (g : B.isometryGroup)
    (F : P →ₛₗ[τ.toRingHom] P →ₗ[K] K) (J : N →ₛₗ[τ.toRingHom] N →ₗ[K] K)
    (hB : B.SeparatingLeft) (hA : A ≤ A.orthogonalBilin B) (hr : Function.Surjective r)
    (hker : r.ker = A.comap (A.orthogonalBilin B).subtype)
    (hform : ∀ x y : A.orthogonalBilin B,
      B x y = F (r x).1 (r y).1 - J (r x).2 (r y).2)
    (hdef : ∀ x : P × N, F x.1 x.1 + J x.2 x.2 = 0 → x = 0) :
    let C := (F.comp (fst K P N)).compl₂ (fst K P N) + (J.comp (snd K P N)).compl₂ (snd K P N)
    ∃! u : C.isometryGroup, ∀ x y : P × N,
      (x, y) ∈ B.isometryLink A r g.val ↔ u.val (x.1, y.2) = (y.1, x.2) := by
  intro C
  let D := (F.comp (fst K P N)).compl₂ (fst K P N) - (J.comp (snd K P N)).compl₂ (snd K P N)
  let L := B.isometryLink A r g.val
  let e : ((P × N) × (P × N)) ≃ₗ[K] ((P × N) × (P × N)) :=
    { toFun := fun z ↦ ((z.1.1, z.2.2), (z.2.1, z.1.2))
      invFun := fun z ↦ ((z.1.1, z.2.2), (z.2.1, z.1.2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have e_apply (x : (P × N) × (P × N)) : e x = ((x.1.1, x.2.2), (x.2.1, x.1.2)) := rfl
  have he (x y : (P × N) × (P × N)) : C.doubled (e x) (e y) = D.doubled x y := by
    simp only [C, D, e_apply, doubled_apply, LinearMap.add_apply, LinearMap.sub_apply, compl₂_apply,
      comp_apply, fst_apply, snd_apply]
    abel
  have hL := B.isometryLink_le_orthogonalBilin_doubled r g (C := D)
    (fun x y ↦ (hform x y).symm)
  have hmap : L.map e.toLinearMap ≤ (L.map e.toLinearMap).orthogonalBilin C.doubled := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
    exact (he x y).trans (hL hy x hx)
  let : FiniteDimensional K (P × N) := FiniteDimensional.of_surjective r hr
  have hdim : finrank K (L.map e.toLinearMap) = finrank K (P × N) :=
    (e.finrank_map_eq L).trans (B.finrank_isometryLink r g hB hA hr hker)
  have hC (x : P × N) (hx : C x x = 0) : x = 0 := hdef x hx
  obtain ⟨u, hu, huniq⟩ :=
    (L.map e.toLinearMap).existsUnique_isometry_graph_eq_of_le_orthogonalBilin_doubled
      hC hmap hdim.ge
  have mem_map (z : (P × N) × (P × N)) : e z ∈ L.map e.toLinearMap ↔ z ∈ L := by
    rw [Submodule.mem_map_equiv, e.symm_apply_apply]
  refine ⟨u, fun x y ↦ ?_, fun v hv ↦ huniq v ?_⟩
  · rw [← mem_map (x, y), ← hu]
    exact (mem_graph_iff _ _).trans eq_comm
  · ext z
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [mem_map, hv x.1 x.2]
    exact (mem_graph_iff _ _).trans eq_comm

end LinearMap
