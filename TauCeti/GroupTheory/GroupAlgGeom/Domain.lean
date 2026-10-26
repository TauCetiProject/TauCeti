/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CSA
public import TauCeti.GroupTheory.GroupAlgGeom.Basic

/-!
# Zero divisors and domains over a group of coefficients

Let `H` be a group receiving coefficients from `G` through `ι : G →* H`. A nonidentity element
`x : H` is a *`G`-zero divisor* when there is a nonidentity `y : H` such that `x` commutes with
every conjugate `ι g * y * (ι g)⁻¹` of `y` by a coefficient, and `H` is a *`G`-domain* when it has
no `G`-zero divisors. Taking for `ι` the identity of `H`, these are the zero divisors and the
domains of the group `H` itself.

In a `G`-domain, for any two nonidentity elements `x` and `y` some commutator
`⁅x, ι g * y * (ι g)⁻¹⁆` is nontrivial. This is what makes the union of two algebraic sets over a
`G`-domain algebraic, cut out by such commutators of their equations; domains thus appear as the
hypothesis under which the closed sets of the Zariski topology are the algebraic sets, and in the
irreducibility criterion for algebraic sets over groups.

Being a domain is not torsion-freeness but a strong form of noncommutativity: a nontrivial group
with nontrivial centre, in particular a nontrivial abelian group, is never a domain, and neither
is a direct product of two nontrivial groups. On the other hand a CSA group in which two
coefficients do not commute is a `G`-domain (Baumslag–Myasnikov–Remeslennikov, Proposition 1).
Hence a nonabelian free group `F` is a domain, and every CSA group containing `F` is an
`F`-domain. The noncommuting coefficients cannot be dropped: `Multiplicative ℤ` is CSA, but it is
not a domain over any coefficients.

The coefficient map need not be injective, matching `TauCeti.GroupAlgGeom.IsSeparatedBy`.

## Main definitions

* `TauCeti.GroupAlgGeom.IsZeroDivisor ι x`: `x` is a `G`-zero divisor of `H`.
* `TauCeti.GroupAlgGeom.IsGDomain ι`: `H` has no `G`-zero divisors.

## Main results

* `TauCeti.GroupAlgGeom.isGDomain_iff`: `H` is a `G`-domain iff for any nonidentity `x` and `y`
  some coefficient conjugate of `y` does not commute with `x`.
* `TauCeti.GroupAlgGeom.IsGDomain.mono`: enlarging the image of the coefficients preserves being
  a domain; in particular a `G`-domain is a domain.
* `TauCeti.GroupAlgGeom.IsGDomain.of_injective`: a group embedding into a `G`-domain by a
  coefficient-preserving map is a `G`-domain.
* `TauCeti.GroupAlgGeom.IsGDomain.of_isCSA`: a CSA group with two noncommuting coefficients is a
  `G`-domain.
* `IsFreeGroup.isGDomain_id`, `FreeGroup.isGDomain_id`: nonabelian free groups are domains.
* `TauCeti.GroupAlgGeom.not_isGDomain_of_center_ne_bot`,
  `TauCeti.GroupAlgGeom.not_isGDomain_prod`: groups with nontrivial centre and products of two
  nontrivial groups are not domains over any coefficients.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.1, Definition 1, Proposition 1 and Corollary 1.
-/

public section

open Group

namespace TauCeti.GroupAlgGeom

variable {G G' H K : Type*} [Group G] [Group G'] [Group H] [Group K]

/-- A nonidentity `x : H` is a zero divisor over `G`, for the coefficient map `ι`, when some
nonidentity `y : H` has all its conjugates `ι g * y * (ι g)⁻¹` by coefficients commuting with
`x`. -/
def IsZeroDivisor (ι : G →* H) (x : H) : Prop :=
  x ≠ 1 ∧ ∃ y : H, y ≠ 1 ∧ ∀ g : G, Commute x (ι g * y * (ι g)⁻¹)

/-- `H` is a domain over `G`, for the coefficient map `ι`, when it has no zero divisors over `G`.
For `ι` the identity of `H`, this says that `H` is a domain. -/
def IsGDomain (ι : G →* H) : Prop :=
  ∀ x : H, ¬IsZeroDivisor ι x

/-- The defining condition for a zero divisor over `G`. -/
theorem isZeroDivisor_def (ι : G →* H) (x : H) :
    IsZeroDivisor ι x ↔ x ≠ 1 ∧ ∃ y : H, y ≠ 1 ∧ ∀ g : G, Commute x (ι g * y * (ι g)⁻¹) :=
  Iff.rfl

/-- The defining condition for a domain over `G`. -/
theorem isGDomain_def (ι : G →* H) : IsGDomain ι ↔ ∀ x : H, ¬IsZeroDivisor ι x :=
  Iff.rfl

/-- `H` is a domain over `G` exactly when, for any two nonidentity elements `x` and `y`, some
conjugate of `y` by a coefficient does not commute with `x`. -/
theorem isGDomain_iff (ι : G →* H) :
    IsGDomain ι ↔
      ∀ x y : H, x ≠ 1 → y ≠ 1 → ∃ g : G, ¬Commute x (ι g * y * (ι g)⁻¹) := by
  simp only [isGDomain_def, isZeroDivisor_def, not_and, not_exists, not_forall]
  exact ⟨fun h x y hx hy => h x hx y hy, fun h x hx y hy => h x y hx hy⟩

/-- Every group with trivial underlying type is a domain over any coefficients. -/
theorem isGDomain_of_subsingleton [Subsingleton H] (ι : G →* H) : IsGDomain ι :=
  fun x hx => hx.1 (Subsingleton.elim x 1)

namespace IsGDomain

/-- A domain over `G` is a domain over any coefficients with a larger image: commuting with more
conjugates is harder. In particular a domain over `G` is a domain over itself. -/
theorem mono {ι : G →* H} {ι' : G' →* H} (h : IsGDomain ι) (hle : ι.range ≤ ι'.range) :
    IsGDomain ι' := by
  rintro x ⟨hx, y, hy, hxy⟩
  refine h x ⟨hx, y, hy, fun g => ?_⟩
  obtain ⟨g', hg'⟩ := hle ⟨g, rfl⟩
  rw [← hg']
  exact hxy g'

/-- The source of an injective coefficient-preserving map into a domain over `G` is a domain over
`G`. -/
theorem of_injective {ιH : G →* H} {ιK : G →* K} (h : IsGDomain ιK) (f : GHom ιH ιK)
    (hf : Function.Injective f) : IsGDomain ιH := by
  rintro x ⟨hx, y, hy, hxy⟩
  refine h (f x) ⟨(map_ne_one_iff f hf).2 hx, f y, (map_ne_one_iff f hf).2 hy, fun g => ?_⟩
  simpa using (hxy g).map f

/-- **CSA groups are domains** (Baumslag–Myasnikov–Remeslennikov, Proposition 1). A CSA group in
which the images of two coefficients do not commute is a domain over these coefficients. -/
theorem of_isCSA {ι : G →* H} (hH : IsCSA H) {a b : G} (hab : ¬Commute (ι a) (ι b)) :
    IsGDomain ι := by
  rintro x ⟨hx, y, hy, hxy⟩
  -- The centralizer `M` of `x` is abelian and malnormal, and contains `y` together with all its
  -- conjugates by coefficients. By malnormality it contains every coefficient, so `M` being
  -- abelian makes all coefficients commute.
  have hyM : y ∈ Subgroup.centralizer {x} :=
    Subgroup.mem_centralizer_singleton_iff.2 (by simpa using (hxy 1).eq.symm)
  have hmem (g : G) : ι g ∈ Subgroup.centralizer {x} := by
    by_contra hg
    exact (hH.centralizer_isTISubgroup hx).conj_notMem hg hyM hy
      (Subgroup.mem_centralizer_singleton_iff.2 (hxy g).eq.symm)
  have := hH.centralizer_isMulCommutative hx
  exact hab (setLike_mul_comm (hmem a) (hmem b))

/-- A CSA group receiving a nonabelian group of coefficients injectively is a domain over it. -/
theorem of_isCSA_of_injective {ι : G →* H} (hH : IsCSA H) (hι : Function.Injective ι)
    (hG : ¬IsMulCommutative G) : IsGDomain ι := by
  obtain ⟨a, b, hab⟩ : ∃ a b : G, ¬Commute a b := by
    simpa [isMulCommutative_iff, commute_iff_eq] using hG
  exact of_isCSA hH fun h => hab (h.of_map hι)

end IsGDomain

/-- A group with a nonidentity central element is not a domain over any coefficients: the central
element commutes with every conjugate of itself. -/
theorem not_isGDomain_of_center_ne_bot (ι : G →* H) (hH : Subgroup.center H ≠ ⊥) :
    ¬IsGDomain ι := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have hz1 : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  exact fun h => h z ⟨hz1, z, hz1, fun g => (Subgroup.mem_center_iff.mp hz _).symm⟩

/-- A nontrivial abelian group is not a domain over any coefficients, although it may be
torsion-free: being a domain is a noncommutativity condition. -/
theorem not_isGDomain_of_isMulCommutative [IsMulCommutative H] [Nontrivial H] (ι : G →* H) :
    ¬IsGDomain ι :=
  not_isGDomain_of_center_ne_bot ι (by simp [Subgroup.center_eq_top])

/-- A direct product of two nontrivial groups is not a domain over any coefficients: `(x, 1)`
commutes with every conjugate of `(1, y)`. -/
theorem not_isGDomain_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] [Nontrivial H₁] [Nontrivial H₂]
    (ι : G →* H₁ × H₂) : ¬IsGDomain ι := by
  obtain ⟨a, ha⟩ := exists_ne (1 : H₁)
  obtain ⟨b, hb⟩ := exists_ne (1 : H₂)
  exact fun h => h (a, 1) ⟨by simpa using ha, (1, b), by simpa using hb,
    fun g => Commute.prod (by simp) (by simp)⟩

end TauCeti.GroupAlgGeom

open TauCeti.GroupAlgGeom

/-- **Nonabelian free groups are domains** (Baumslag–Myasnikov–Remeslennikov, Corollary 1). -/
theorem IsFreeGroup.isGDomain_id {F : Type*} [Group F] [IsFreeGroup F]
    (hF : ¬IsMulCommutative F) : IsGDomain (MonoidHom.id F) :=
  IsGDomain.of_isCSA_of_injective IsFreeGroup.isCSA Function.injective_id hF

/-- The free group on at least two generators is a domain. -/
theorem FreeGroup.isGDomain_id {α : Type*} [Nontrivial α] :
    IsGDomain (MonoidHom.id (FreeGroup α)) :=
  IsFreeGroup.isGDomain_id fun h =>
    not_subsingleton α (FreeGroup.isMulCommutative_iff_subsingleton.mp h)
