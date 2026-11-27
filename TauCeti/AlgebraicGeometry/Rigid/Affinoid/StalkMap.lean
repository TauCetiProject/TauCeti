/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Comap
public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Stalk

/-!
# Stalk maps of morphisms of affinoid spaces

A `K`-algebra map `φ : A → B` of affinoid algebras is a morphism `Sp B → Sp A`. For an affinoid
subdomain `U` of `Sp A` the inverse image `φ⁻¹(U)` is an affinoid subdomain of `Sp B`, and the
universal property of `U` pulls functions back along `φ`, from `𝒪(U)` to `𝒪(φ⁻¹(U))`
(`TauCeti.AffinoidSubdomain.comapSections`), compatibly with restriction. Passing to the colimits
over the affinoid neighbourhoods of a classical point `y` of `Sp B` and of its image gives the
stalk map

`φ*_y : 𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}`

(`AlgHom.stalkMap`), which sends the germ of `f ∈ 𝒪(U)` to the germ of its pullback. It is a local
homomorphism of local rings, compatible with the germ maps `A → 𝒪_{Sp A,φ(y)}` and
`B → 𝒪_{Sp B,y}`, with identities and with composition.

For the inclusion `φ : A → B` of an affinoid subdomain `U` of `Sp A`, every stalk map is bijective
(`TauCeti.IsAffinoidSubdomainMap.bijective_stalkMap`): by transitivity, every affinoid
neighbourhood `W` of `y` in `Sp B` is, through `φ`, an affinoid neighbourhood of `φ(y)` in `Sp A`
contained in `U`, with the same coordinate algebra, and its inverse image under `φ` is `W` again.

A surjective stalk map makes every infinitesimal neighbourhood `B ⧸ 𝔪_yⁿ` a quotient of `A`.
The stalk maps are what the locally closed and open immersions of affinoid spaces are defined by.

## Main definitions

* `AlgHom.stalkMap φ y`: the stalk map `𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}`.

## Main results

* `AlgHom.stalkMap_germ`: the stalk map sends the germ of `f` to the germ of its pullback.
* `AlgHom.stalkMap_toStalk`: the stalk map is compatible with the germ maps of `A` and `B`.
* `AlgHom.isLocalHom_stalkMap`: the stalk map is a local homomorphism.
* `AlgHom.stalkMap_id_germ`, `AlgHom.stalkMap_comp_germ`: identity and composition.
* `AlgHom.surjective_stalkMap_comp`, `AlgHom.injective_stalkMap_comp`: surjective and injective
  stalk maps compose.
* `AlgHom.exists_sub_mem_pow_of_surjective_stalkMap`: if the stalk map at `y` is surjective, then
  `A → B ⧸ 𝔪_yⁿ` is surjective for every `n`.
* `TauCeti.IsAffinoidSubdomainMap.bijective_stalkMap`: the inclusion of an affinoid subdomain
  induces bijections of stalks.

## References

* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105,
  Springer, 2014, §4.1, pp. 65–66, and §4.2, p. 69.
-/

public section

open IsLocalRing TauCeti TauCeti.AffinoidSubdomain

namespace AlgHom

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C]
  [hA : Fact (IsAffinoidAlgebra K A)] [hB : Fact (IsAffinoidAlgebra K B)]
  [hC : Fact (IsAffinoidAlgebra K C)]

/-- The stalk map `φ*_y : 𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` of analytic stalks induced by
`φ : A → B` at a classical point `y` of `Sp B`: the germ at `φ(y)` of a section `f` over `U` goes
to the germ at `y` of its pullback `TauCeti.AffinoidSubdomain.comapSections` to `φ⁻¹(U)`. -/
noncomputable def stalkMap (φ : A →ₐ[K] B) (y : MaximalSpectrum B) :
    stalk K (hB.out.maximalSpectrumComap φ y) →+* stalk K y :=
  stalkLift (fun U hy ↦ (germ (U.comap φ) ((mem_comap U φ y).mpr hy)).comp
      (U.comapSections φ).toRingHom)
    (fun U V hUV hy ↦ RingHom.ext fun f ↦ by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← AlgHom.comp_apply, comapSections_restrict, AlgHom.comp_apply, germ_restrict])

/-- **The stalk map on germs.** The stalk map sends the germ at `φ(y)` of a section `f` over `U`
to the germ at `y` of its pullback to `φ⁻¹(U)`. -/
@[simp]
theorem stalkMap_germ (φ : A →ₐ[K] B) {y : MaximalSpectrum B} (U : AffinoidSubdomain K A)
    (hy : hB.out.maximalSpectrumComap φ y ∈ U) (f : U.sections) :
    φ.stalkMap y (germ U hy f) =
      germ (U.comap φ) ((mem_comap U φ y).mpr hy) (U.comapSections φ f) :=
  stalkLift_germ _ _ hy f

/-- The stalk map is compatible with the germ maps of `A` and `B`. -/
@[simp]
theorem stalkMap_toStalk (φ : A →ₐ[K] B) (y : MaximalSpectrum B) (a : A) :
    φ.stalkMap y (toStalk K _ a) = toStalk K y (φ a) := by
  rw [toStalk_apply, stalkMap_germ, comapSections_toSections, germ_toSections]

/-- The germ map of `B` composed with `φ` factors through the stalk map. -/
theorem stalkMap_comp_toStalk (φ : A →ₐ[K] B) (y : MaximalSpectrum B) :
    (φ.stalkMap y).comp (toStalk K _) = (toStalk K y).comp φ.toRingHom :=
  RingHom.ext (φ.stalkMap_toStalk y)

/-- **Stalk maps are local homomorphisms.** -/
instance isLocalHom_stalkMap (φ : A →ₐ[K] B) (y : MaximalSpectrum B) :
    IsLocalHom (φ.stalkMap y) := by
  refine ((local_hom_tfae _).out 1 3).mpr ?_
  rw [maximalIdeal_stalk, Ideal.map_map, stalkMap_comp_toStalk, ← Ideal.map_map,
    maximalIdeal_stalk]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr
    (IsAffinoidAlgebra.maximalSpectrumComap_asIdeal _ _ _).le)

/-- **The stalk map of the identity is the identity**, evaluated on germs; the points `id(x)` and
`x` of `Sp A` are equal, although not syntactically. -/
theorem stalkMap_id_germ {x : MaximalSpectrum A} (U : AffinoidSubdomain K A)
    (hx : hA.out.maximalSpectrumComap (AlgHom.id K A) x ∈ U) (f : U.sections) :
    (AlgHom.id K A).stalkMap x (germ U hx f) =
      germ U (by rwa [IsAffinoidAlgebra.maximalSpectrumComap_id, id] at hx) f := by
  have hx' : x ∈ U := by rwa [IsAffinoidAlgebra.maximalSpectrumComap_id, id] at hx
  rw [stalkMap_germ, ← germ_restrict (le_of_eq U.comap_id.symm) hx', ← AlgHom.comp_apply,
    restrict_comapSections_id, AlgHom.id_apply]

/-- **Stalk maps compose.** The stalk map of `ψ ∘ φ` at `z` is the stalk map of `φ` at `ψ(z)`
followed by that of `ψ` at `z`, evaluated on germs; the two points `(ψ ∘ φ)(z)` and `φ(ψ(z))` of
`Sp A` are equal, although not syntactically. -/
theorem stalkMap_comp_germ (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) {z : MaximalSpectrum C}
    (U : AffinoidSubdomain K A) (hz : hC.out.maximalSpectrumComap (ψ.comp φ) z ∈ U)
    (f : U.sections) :
    (ψ.comp φ).stalkMap z (germ U hz f) =
      ψ.stalkMap z (φ.stalkMap _ (germ U (by
        rwa [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out] at hz) f)) := by
  rw [stalkMap_germ, stalkMap_germ, stalkMap_germ, ← AlgHom.comp_apply _ (U.comapSections φ),
    ← comapSections_comp, AlgHom.comp_apply, germ_restrict]

/-- A composite of surjective stalk maps is surjective. -/
theorem surjective_stalkMap_comp {φ : A →ₐ[K] B} {ψ : B →ₐ[K] C} {z : MaximalSpectrum C}
    (hφ : Function.Surjective (φ.stalkMap (hC.out.maximalSpectrumComap ψ z)))
    (hψ : Function.Surjective (ψ.stalkMap z)) :
    Function.Surjective ((ψ.comp φ).stalkMap z) := by
  intro s
  obtain ⟨t, rfl⟩ := hψ s
  obtain ⟨r, rfl⟩ := hφ t
  obtain ⟨U, hx, f, rfl⟩ := exists_germ_eq r
  have hz : hC.out.maximalSpectrumComap (ψ.comp φ) z ∈ U := by
    rwa [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]
  exact ⟨germ U hz f, stalkMap_comp_germ φ ψ U hz f⟩

/-- A composite of injective stalk maps is injective. -/
theorem injective_stalkMap_comp {φ : A →ₐ[K] B} {ψ : B →ₐ[K] C} {z : MaximalSpectrum C}
    (hφ : Function.Injective (φ.stalkMap (hC.out.maximalSpectrumComap ψ z)))
    (hψ : Function.Injective (ψ.stalkMap z)) :
    Function.Injective ((ψ.comp φ).stalkMap z) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨U, hz, f, rfl⟩ := exists_germ_eq s
  rw [stalkMap_comp_germ, map_eq_zero_iff _ hψ, map_eq_zero_iff _ hφ, germ_eq_zero_iff] at hs
  obtain ⟨W, hWU, hxW, hW⟩ := hs
  refine (germ_eq_zero_iff hz f).mpr ⟨W, hWU, ?_, hW⟩
  rwa [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]

/-- A surjective stalk map `𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` makes every infinitesimal neighbourhood
`B ⧸ 𝔪_yⁿ` of `y` a quotient of `A`: every `b ∈ B` is congruent to some `φ a` modulo `𝔪_yⁿ`. -/
theorem exists_sub_mem_pow_of_surjective_stalkMap {φ : A →ₐ[K] B} {y : MaximalSpectrum B}
    (h : Function.Surjective (φ.stalkMap y)) (n : ℕ) (b : B) :
    ∃ a : A, b - φ a ∈ y.asIdeal ^ n := by
  obtain ⟨s, hs⟩ := h (toStalk K y b)
  obtain ⟨a', ha'⟩ := (quotientPowEquiv K _ n).surjective (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  rw [quotientPowEquiv_mk, Ideal.Quotient.eq, ← neg_mem_iff, neg_sub] at ha'
  refine ⟨a, Ideal.Quotient.eq_zero_iff_mem.mp ((quotientPowEquiv K y n).injective ?_)⟩
  -- The germ of `b - φ a` is the image of `s - a ∈ 𝔪ⁿ` under the local stalk map.
  rw [quotientPowEquiv_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hs,
    ← stalkMap_toStalk, ← map_sub]
  have hmem := Ideal.mem_map_of_mem (φ.stalkMap y) ha'
  rw [Ideal.map_pow] at hmem
  exact pow_le_pow_left' (map_maximalIdeal_le (φ.stalkMap y)) n hmem

end AlgHom

namespace TauCeti.IsAffinoidSubdomainMap

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [hA : Fact (IsAffinoidAlgebra K A)] [hB : Fact (IsAffinoidAlgebra K B)]
  {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}

omit hB in
/-- The affinoid subdomain of `Sp A` given by the image of an affinoid subdomain `W` of `Sp B`,
for `φ : A → B` representing an affinoid subdomain of `Sp A`. -/
private noncomputable def imageSubdomain (hU : IsAffinoidSubdomainMap φ U)
    (W : AffinoidSubdomain K B) : AffinoidSubdomain K A :=
  ofMap (hU.comp hA.out W.isAffinoidSubdomainMap)

omit hB in
/-- The image subdomain has the coordinate algebra of `W`. -/
private noncomputable def imageSectionsAlgEquiv (hU : IsAffinoidSubdomainMap φ U)
    (W : AffinoidSubdomain K B) : (imageSubdomain hU W).sections ≃ₐ[K] W.sections :=
  (imageSubdomain hU W).sectionsAlgEquiv (by
    rw [imageSubdomain, coe_ofMap]
    exact hU.comp hA.out W.isAffinoidSubdomainMap)

omit hB in
private theorem imageSectionsAlgEquiv_toSections (hU : IsAffinoidSubdomainMap φ U)
    (W : AffinoidSubdomain K B) (a : A) :
    imageSectionsAlgEquiv hU W ((imageSubdomain hU W).toSections a) = W.toSections (φ a) :=
  ((imageSubdomain hU W).sectionsAlgEquiv_toSections _ a).trans (AlgHom.comp_apply _ _ _)

private theorem mem_imageSubdomain (hU : IsAffinoidSubdomainMap φ U)
    {W : AffinoidSubdomain K B} {y : MaximalSpectrum B} (hy : y ∈ W) :
    hB.out.maximalSpectrumComap φ y ∈ imageSubdomain hU W := by
  rw [imageSubdomain, mem_ofMap]
  exact ⟨y, hy, rfl⟩

private theorem imageSubdomain_le (hU : IsAffinoidSubdomainMap φ U)
    {W : AffinoidSubdomain K B} {V : AffinoidSubdomain K A} (hWV : W ≤ V.comap φ) :
    imageSubdomain hU W ≤ V := by
  intro x hx
  rw [imageSubdomain, mem_ofMap] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact (mem_comap V φ w).mp (hWV hw)

/-- Under the identification of coordinate algebras, restriction from `V` to the image of
`W ≤ φ⁻¹(V)` is pullback along `φ` followed by restriction to `W`. -/
private theorem imageSectionsAlgEquiv_restrict (hU : IsAffinoidSubdomainMap φ U)
    {W : AffinoidSubdomain K B} {V : AffinoidSubdomain K A} (hWV : W ≤ V.comap φ)
    (f : V.sections) :
    imageSectionsAlgEquiv hU W (restrict (imageSubdomain_le hU hWV) f) =
      restrict hWV (V.comapSections φ f) := by
  have : (imageSectionsAlgEquiv hU W).toAlgHom.comp (restrict (imageSubdomain_le hU hWV)) =
      (restrict hWV).comp (V.comapSections φ) := by
    refine V.isAffinoidSubdomainMap.algHom_ext W.isAffinoidAlgebra (AlgHom.ext fun a ↦ ?_)
    simp only [AlgHom.comp_apply, restrict_toSections,
      comapSections_toSections]
    exact imageSectionsAlgEquiv_toSections hU W a
  exact AlgHom.congr_fun this f

/-- **Inclusions of affinoid subdomains induce isomorphisms of stalks.** If `φ : A → B`
represents an affinoid subdomain of `Sp A`, then every stalk map
`𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` is bijective. -/
theorem bijective_stalkMap (hU : IsAffinoidSubdomainMap φ U) (y : MaximalSpectrum B) :
    Function.Bijective (φ.stalkMap y) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun s hs ↦ ?_, fun s ↦ ?_⟩
  · -- A germ whose pullback vanishes on `W ∋ y` vanishes on the image of `W`.
    obtain ⟨V, hx, f, rfl⟩ := exists_germ_eq s
    rw [AlgHom.stalkMap_germ, germ_eq_zero_iff] at hs
    obtain ⟨W, hWV, hyW, hW⟩ := hs
    refine (germ_eq_zero_iff hx f).mpr ⟨imageSubdomain hU W, imageSubdomain_le hU hWV,
      mem_imageSubdomain hU hyW, (imageSectionsAlgEquiv hU W).injective ?_⟩
    rw [imageSectionsAlgEquiv_restrict hU hWV, hW, map_zero]
  · -- A germ on `W ∋ y` is the pullback of the corresponding germ on the image of `W`.
    obtain ⟨W, hy, g, rfl⟩ := exists_germ_eq s
    have hWW : W ≤ (imageSubdomain hU W).comap φ := fun w hw ↦
      (mem_comap _ φ w).mpr (mem_imageSubdomain hU hw)
    refine ⟨germ _ (mem_imageSubdomain hU hy) ((imageSectionsAlgEquiv hU W).symm g), ?_⟩
    rw [AlgHom.stalkMap_germ, ← germ_restrict hWW hy, ← imageSectionsAlgEquiv_restrict hU hWW,
      restrict_refl, AlgHom.id_apply, AlgEquiv.apply_symm_apply]

end TauCeti.IsAffinoidSubdomainMap
