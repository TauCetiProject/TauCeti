/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.PrimitiveIdempotent

/-!
# Principal left ideals in a quotient ring

For a two-sided ideal `I` of a ring `A`, the quotient map restricts to a surjection from `Ae`
to `(A/I) ē`. Its kernel is `I ∩ Ae`. If `e` is idempotent, this intersection is exactly `Ie`,
so the vertex projectives of a bound quiver are obtained from the path-algebra projectives by
imposing the relations on them. The comparison is `A`-linear, with the target acted on through
the quotient map.

The generator `e` is the first argument, as in `TauCeti.spanSingletonGenerator e`.
Use `TauCeti.spanSingletonQuotientMap e I` for the restriction and
`TauCeti.spanSingletonRelationMap e I` for right multiplication of the relations by `e`.
The kernel is characterized by `TauCeti.ker_spanSingletonQuotientMap e I`; when `e` is
idempotent, `TauCeti.range_spanSingletonRelationMap e I` identifies it with the relation-map range.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Chapter III, Section 2, for vertex projectives of bound quivers.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] (e : A) (I : Ideal A) [I.IsTwoSided]

/-- The restriction of the quotient map to the principal left ideal `Ae`. The target is an
`A`-module through the quotient map `A → A/I`. -/
noncomputable def spanSingletonQuotientMap :
    (Ideal.span {e} : Ideal A) →ₗ[A] (Ideal.span {Ideal.Quotient.mk I e} : Ideal (A ⧸ I)) :=
  LinearMap.codRestrict
    ((Ideal.span {Ideal.Quotient.mk I e} : Ideal (A ⧸ I)).restrictScalars A)
    (I.mkQ.domRestrict (Ideal.span {e})) fun x => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.2
    exact Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk I a, by rw [← map_mul, ha]; rfl⟩

@[simp]
theorem coe_spanSingletonQuotientMap (x : (Ideal.span {e} : Ideal A)) :
    (spanSingletonQuotientMap e I x : A ⧸ I) = Ideal.Quotient.mk I x := (rfl)

/-- Every element of the principal left ideal in the quotient lifts to the original one. -/
theorem spanSingletonQuotientMap_surjective :
    Function.Surjective (spanSingletonQuotientMap e I) := by
  intro y
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp y.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨⟨a * e, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩, Subtype.ext ?_⟩
  simpa only [coe_spanSingletonQuotientMap, map_mul] using hb

/-- The restricted quotient map kills exactly the elements of `Ae` lying in `I`. -/
theorem ker_spanSingletonQuotientMap :
    LinearMap.ker (spanSingletonQuotientMap e I) = Submodule.comap (Ideal.span {e}).subtype I := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  rw [← Subtype.val_inj, coe_spanSingletonQuotientMap, Submodule.coe_zero,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The relation map `I → Ae`, given by right multiplication by `e`. Its range is `Ie`. -/
def spanSingletonRelationMap : I →ₗ[A] (Ideal.span {e} : Ideal A) :=
  LinearMap.codRestrict (Ideal.span {e}) ((LinearMap.mulRight A e).domRestrict I)
    fun x => Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩

omit [I.IsTwoSided] in
@[simp]
theorem coe_spanSingletonRelationMap (x : I) :
    (spanSingletonRelationMap e I x : A) = (x : A) * e := (rfl)

/-- For an idempotent, the kernel is precisely `Ie`, rather than just `I ∩ Ae`. -/
theorem range_spanSingletonRelationMap (he : IsIdempotentElem e) :
    LinearMap.range (spanSingletonRelationMap e I) =
      Submodule.comap (Ideal.span {e}).subtype I := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact I.mul_mem_right e y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subtype.ext ((mem_span_singleton_iff_mul_eq_self he).mp x.2)⟩

end TauCeti
