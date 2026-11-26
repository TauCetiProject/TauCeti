/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.DoubleCoset.Mass
import TauCeti.Algebra.Module.Rat
import TauCeti.GroupTheory.DoubleCoset.Finite
public import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Weighted class sums and class integrals

Let `G` be a group with subgroups `Γ` and `K`. For `f : G → W` with values in a `ℚ`-vector space,
left invariant under `Γ` and right invariant under `K`, the **class sum** is

`S_{Γ,K}(f) = ∑_{Γ g K} f(g) / #Γ_g`,  `Γ_g = Γ ∩ g K g⁻¹`,

the sum over the double cosets `Γ \ G / K` (`TauCeti.doubleCosetClassSum`). A class with infinite
stabiliser has weight `0`. Through the bijection of `Γ \ G / K` with the orbits of `K` on `G ⧸ Γ`,
it is the weighted orbit sum `TauCeti.orbitSum` of the induced function on the orbit space
(`TauCeti.doubleCosetClassSum_eq_orbitSum`), and `S_{Γ,K}(1)` is the mass
`TauCeti.orbitMass K (G ⧸ Γ)`.

**Change of level** (`TauCeti.doubleCosetClassSum_comp_mul_right`): if `a⁻¹ K' a ⊂ K` has finite
index, then `S_{Γ,K'}(g ↦ f(g a)) = [K : a⁻¹ K' a] · S_{Γ,K}(f)`. Above the class of `g a` the
classes of `K'` are the orbits of `Γ_g` on `K / a⁻¹ K' a`, and the orbit-stabiliser count gives the
index; this is the index formula `TauCeti.orbitSum_comp_map_of_le` transported along conjugation by
`a`.

For a topological group, the pair `(Γ, K)` has **finite type**
(`TauCeti.HasFiniteType Γ K`) if `K` is compact and open, `Γ \ G / K` is finite and every `Γ_g`
is finite. For `f` left `Γ`-invariant and fixed on the right by an open subgroup, the **class
integral** `I_{Γ,K}(f) = [K : J]⁻¹ S_{Γ,J}(f)` (`TauCeti.classIntegral`), computed at any open
`J ⊂ K` fixing `f` (`TauCeti.classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum`), is the
integral of `f` over `Γ \ G` for the Haar measure with `vol K = 1`. It is additive, commutes with
additive maps of the values, and is invariant under right translation
(`TauCeti.classIntegral_comp_mul_right`).

## Main definitions

* `TauCeti.doubleCosetClassSum Γ K f`: the weighted class sum `∑_{Γ g K} f(g) / #(Γ ∩ g K g⁻¹)`.
* `TauCeti.HasFiniteType Γ K`: `(Γ, K)` has finite type.
* `TauCeti.classIntegral Γ K f`: the class integral `[K : J]⁻¹ S_{Γ,J}(f)`,
  `J = K ∩ rightTranslationStabilizer f`, where `TauCeti.rightTranslationStabilizer f` (from
  `TauCeti.Topology.Algebra.Group.LocallyConstant`) is the subgroup of `k` with `f (g * k) = f g`
  for all `g`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press, 1971, ch. 3.
* B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93.
* M. Greenberg and J. Voight, *Lattice methods for algebraic modular forms on classical groups*,
  in *Computations with modular forms*, Springer, 2014.

The definitions and the statements of change of level and of the properties of the class integral
are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic PBC), `src/Lib/Adelic/Hecke/Basic.lean` (`New.classSum`, `New.classAut`,
`New.classSum_eq_finsum_of_rep`) and `src/Lib/Adelic/Hecke/ClassSums.lean` (`New.HasFiniteType`,
`New.classIntegral`, `New.classSum_eq_relIndex_smul`,
`New.classIntegral_eq_classSum_mul`, `New.classIntegral_sum`, `New.classIntegral_add`,
`New.classIntegral_map_mul_right`); the proofs here go through the weighted orbit sums of
`TauCeti/GroupTheory/DoubleCoset/Mass.lean`.
-/

public section

open MulAction Pointwise

namespace TauCeti

variable {G W W' : Type*} [Group G] [AddCommGroup W] [Module ℚ W] [AddCommGroup W'] [Module ℚ W']

/-! ### Class sums -/

section ClassSum

variable (Γ K : Subgroup G)

/-- **The weighted class sum** `S_{Γ,K}(f) = ∑_{Γ g K} f(g) / #(Γ ∩ g K g⁻¹)` over the double
cosets `Γ \ G / K`, evaluated at the chosen representatives. A class with infinite stabiliser has
weight `0`, and the sum is `0` when its summand has infinite support. For `f` left invariant under
`Γ` and right invariant under `K` any representatives serve
(`TauCeti.doubleCosetClassSum_eq_finsum`). -/
noncomputable def doubleCosetClassSum (f : G → W) : W :=
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) K,
    (Nat.card (mackeySubgroup q.out K Γ) : ℚ)⁻¹ • f q.out

theorem doubleCosetClassSum_def (f : G → W) :
    doubleCosetClassSum Γ K f = ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) K,
      (Nat.card (mackeySubgroup q.out K Γ) : ℚ)⁻¹ • f q.out :=
  (rfl)

variable {Γ K}

/-- **Weighted sums over representatives are weighted orbit sums.** If `F` is a function on the
orbits of `K` on `G ⧸ Γ` with `F (K g⁻¹ Γ) = f g` for every `g`, and `c q` represents the double
coset `q`, then `∑_q f(c q) / #Γ_{c q} = ∑_x c(x)⁻¹ F(x)`. -/
theorem finsum_inv_natCard_mackeySubgroup_smul_eq_orbitSum {f : G → W}
    (F : orbitRel.Quotient K (G ⧸ Γ) → W)
    (hF : ∀ g : G, F (Quotient.mk'' ((g⁻¹ : G) : G ⧸ Γ)) = f g)
    (c : DoubleCoset.Quotient (Γ : Set G) K → G) (hc : ∀ q, DoubleCoset.mk Γ K (c q) = q) :
    ∑ᶠ q, (Nat.card (mackeySubgroup (c q) K Γ) : ℚ)⁻¹ • f (c q) = orbitSum K (G ⧸ Γ) F := by
  rw [orbitSum_def, ← finsum_comp_equiv (doubleCosetQuotientEquivOrbitRelQuotient Γ K)]
  refine finsum_congr fun q ↦ ?_
  conv_rhs => rw [← hc q]
  rw [cardStabilizerOnOrbit_doubleCosetQuotientEquivOrbitRelQuotient_mk,
    natCard_mackeySubgroup_inv_subgroupOf, doubleCosetQuotientEquivOrbitRelQuotient_mk, hF]

/-- **The class sum as a weighted orbit sum.** If `F` is a function on the orbits of `K` on
`G ⧸ Γ` with `F (K g⁻¹ Γ) = f g` for every `g`, then `S_{Γ,K}(f) = ∑_x c(x)⁻¹ F(x)`. -/
theorem doubleCosetClassSum_eq_orbitSum {f : G → W} (F : orbitRel.Quotient K (G ⧸ Γ) → W)
    (hF : ∀ g : G, F (Quotient.mk'' ((g⁻¹ : G) : G ⧸ Γ)) = f g) :
    doubleCosetClassSum Γ K f = orbitSum K (G ⧸ Γ) F :=
  finsum_inv_natCard_mackeySubgroup_smul_eq_orbitSum F hF (fun q ↦ q.out) DoubleCoset.out_eq'

/-- A function that is left invariant under `Γ` and right invariant under `K` induces a function
on the orbits of `K` on `G ⧸ Γ`, with value `f g` at the orbit of `g⁻¹ Γ`. -/
theorem exists_orbitRelQuotient_apply_eq {X : Type*} {f : G → X}
    (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (hr : ∀ k ∈ K, ∀ g, f (g * k) = f g) :
    ∃ F : orbitRel.Quotient K (G ⧸ Γ) → X,
      ∀ g : G, F (Quotient.mk'' ((g⁻¹ : G) : G ⧸ Γ)) = f g := by
  refine ⟨fun p ↦ f ((doubleCosetQuotientEquivOrbitRelQuotient Γ K).symm p).out, fun g ↦ ?_⟩
  dsimp only
  rw [doubleCosetQuotientEquivOrbitRelQuotient_symm_mk, inv_inv]
  obtain ⟨γ, hγ, k, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  rw [h, hr k hk, hl γ hγ]

/-- **Any representatives serve.** For `f` left invariant under `Γ` and right invariant under `K`,
and any representatives `c q` of the double cosets, `S_{Γ,K}(f) = ∑_q f(c q) / #Γ_{c q}`. -/
theorem doubleCosetClassSum_eq_finsum {f : G → W} (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (hr : ∀ k ∈ K, ∀ g, f (g * k) = f g) (c : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hc : ∀ q, DoubleCoset.mk Γ K (c q) = q) :
    doubleCosetClassSum Γ K f =
      ∑ᶠ q, (Nat.card (mackeySubgroup (c q) K Γ) : ℚ)⁻¹ • f (c q) := by
  obtain ⟨F, hF⟩ := exists_orbitRelQuotient_apply_eq hl hr
  rw [doubleCosetClassSum_eq_orbitSum F hF,
    finsum_inv_natCard_mackeySubgroup_smul_eq_orbitSum F hF c hc]

/-- The class sum of the constant `1` is the mass of the class set. -/
theorem doubleCosetClassSum_one :
    doubleCosetClassSum Γ K (fun _ ↦ (1 : ℚ)) = orbitMass K (G ⧸ Γ) := by
  rw [orbitMass_eq_finsum_doubleCoset (fun q ↦ q.out) DoubleCoset.out_eq', doubleCosetClassSum_def]
  simp

/-- **Change of level and of variable.** Let `f` be left invariant under `Γ` and right invariant
under `K`, and let `a⁻¹ K' a ⊂ K` have finite index. Then
`S_{Γ,K'}(g ↦ f (g a)) = [K : a⁻¹ K' a] · S_{Γ,K}(f)`. -/
theorem doubleCosetClassSum_comp_mul_right {K' : Subgroup G} {f : G → W}
    (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (hr : ∀ k ∈ K, ∀ g, f (g * k) = f g) (a : G)
    (hle : MulAut.conj a⁻¹ • K' ≤ K) [(MulAut.conj a⁻¹ • K').IsFiniteRelIndex K] :
    doubleCosetClassSum Γ K' (fun g ↦ f (g * a)) =
      (MulAut.conj a⁻¹ • K').relIndex K • doubleCosetClassSum Γ K f := by
  -- Pull the induced function on `K \ (G ⧸ Γ)` back to `L = a⁻¹ K' a`, where the index formula
  -- applies, and transport it to `K'` along conjugation by `a` and left translation by `a⁻¹`.
  set L := MulAut.conj a⁻¹ • K'
  obtain ⟨F, hF⟩ := exists_orbitRelQuotient_apply_eq hl hr
  let π := Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := G ⧸ Γ) hle)
  let e : G ⧸ Γ ≃ G ⧸ Γ := MulAction.toPerm a⁻¹
  have he (k : K') (x : G ⧸ Γ) : e (k • x) = Subgroup.equivSMul (MulAut.conj a⁻¹) K' k • e x := by
    simp [e, Subgroup.smul_def, mul_smul]
  have h_transport := orbitSum_congr (Subgroup.equivSMul (MulAut.conj a⁻¹) K') e he (F ∘ π)
  rw [orbitSum_comp_map_of_le hle F] at h_transport
  rw [doubleCosetClassSum_eq_orbitSum F hF, ← h_transport]
  refine doubleCosetClassSum_eq_orbitSum _ fun g ↦ ?_
  rw [Function.comp_apply, MulAction.orbitRelQuotientCongr_mk, Function.comp_apply, ← hF (g * a)]
  simp [e, π, mul_inv_rev]

/-- **Change of level.** For `f` left invariant under `Γ` and right invariant under `K`, and
`J ⊂ K` of finite index, `S_{Γ,J}(f) = [K : J] · S_{Γ,K}(f)`. -/
theorem doubleCosetClassSum_eq_relIndex_smul_of_le {J : Subgroup G} {f : G → W}
    (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (hr : ∀ k ∈ K, ∀ g, f (g * k) = f g) (hJK : J ≤ K)
    [J.IsFiniteRelIndex K] :
    doubleCosetClassSum Γ J f = J.relIndex K • doubleCosetClassSum Γ K f := by
  have hJ : MulAut.conj (1 : G)⁻¹ • J = J := by simp
  have : (MulAut.conj (1 : G)⁻¹ • J).IsFiniteRelIndex K := by rw [hJ]; infer_instance
  simpa [hJ] using doubleCosetClassSum_comp_mul_right hl hr 1 (by rw [hJ]; exact hJK)

/-- Class sums over finitely many classes are additive. -/
theorem doubleCosetClassSum_add [Finite (DoubleCoset.Quotient (Γ : Set G) K)] (f f' : G → W) :
    doubleCosetClassSum Γ K (f + f') = doubleCosetClassSum Γ K f + doubleCosetClassSum Γ K f' := by
  simp only [doubleCosetClassSum_def, Pi.add_apply, smul_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

/-- Additive maps of the values commute with class sums over finitely many classes. -/
theorem map_doubleCosetClassSum [Finite (DoubleCoset.Quotient (Γ : Set G) K)] (φ : W →+ W')
    (f : G → W) : φ (doubleCosetClassSum Γ K f) = doubleCosetClassSum Γ K (φ ∘ f) := by
  simp only [doubleCosetClassSum_def, φ.map_finsum (Set.toFinite _), map_rat_smul,
    Function.comp_apply]

end ClassSum

/-! ### Pairs of finite type -/

section FiniteType

variable [TopologicalSpace G]

/-- **`(Γ, K)` has finite type**: `K` is compact and open, `Γ \ G / K` is finite, and every
stabiliser `Γ ∩ g K g⁻¹` is finite. For `G` the finite adelic points of a reductive group compact at
infinity, `Γ` its rational points and `K` a compact open subgroup, this holds by reduction
theory. -/
structure HasFiniteType (Γ K : Subgroup G) : Prop where
  /-- `K` is open. -/
  isOpen : IsOpen (K : Set G)
  /-- `K` is compact. -/
  isCompact : IsCompact (K : Set G)
  /-- There are finitely many classes `Γ g K`. -/
  finite_doubleCoset : Finite (DoubleCoset.Quotient (Γ : Set G) K)
  /-- Every stabiliser `Γ ∩ g K g⁻¹` is finite. -/
  finite_mackeySubgroup (g : G) : Finite (mackeySubgroup g K Γ)

variable {Γ K J : Subgroup G}

/-- The mass of a class set of finite type is positive. -/
theorem HasFiniteType.orbitMass_pos (h : HasFiniteType Γ K) : 0 < orbitMass K (G ⧸ Γ) := by
  have := h.finite_doubleCoset
  have := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) K)
  rw [orbitMass_eq_finsum_doubleCoset (fun q ↦ q.out) DoubleCoset.out_eq',
    finsum_eq_sum_of_fintype]
  refine Finset.sum_pos (fun q _ ↦ ?_) Finset.univ_nonempty
  have := h.finite_mackeySubgroup q.out
  exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)

end FiniteType

/-! ### Class integrals -/

section ClassIntegral

variable (Γ K : Subgroup G)

/-- **The class integral** `I_{Γ,K}(f) = [K : J]⁻¹ S_{Γ,J}(f)` with
`J = K ∩ rightTranslationStabilizer f`.
For `(Γ, K)` of finite type and `f` left `Γ`-invariant with open stabiliser it is the integral of
`f` over `Γ \ G` for the Haar measure with `vol K = 1`, and any open `J ⊂ K` fixing `f` may be used
(`TauCeti.classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum`). -/
noncomputable def classIntegral (f : G → W) : W :=
  ((rightTranslationStabilizer f ⊓ K).relIndex K : ℚ)⁻¹ •
    doubleCosetClassSum Γ (rightTranslationStabilizer f ⊓ K) f

theorem classIntegral_def (f : G → W) :
    classIntegral Γ K f =
      ((rightTranslationStabilizer f ⊓ K).relIndex K : ℚ)⁻¹ •
        doubleCosetClassSum Γ (rightTranslationStabilizer f ⊓ K) f :=
  (rfl)

variable {Γ K}

/-- **The class integral at any level.** For `f` left invariant under `Γ` and `J ⊂ K` of finite
index fixing `f`, `I_{Γ,K}(f) = [K : J]⁻¹ S_{Γ,J}(f)`. -/
theorem classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum {f : G → W}
    (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) {J : Subgroup G} (hJK : J ≤ K)
    (hJf : J ≤ rightTranslationStabilizer f) [J.IsFiniteRelIndex K] :
    classIntegral Γ K f = (J.relIndex K : ℚ)⁻¹ • doubleCosetClassSum Γ J f := by
  -- `J ≤ S = rightTranslationStabilizer f ⊓ K`, `S_{Γ,J}(f) = [S : J] S_{Γ,S}(f)` and
  -- `[K : J] = [K : S][S : J]`.
  set S := rightTranslationStabilizer f ⊓ K
  have hJS : J ≤ S := le_inf hJf hJK
  have hSK : S ≤ K := inf_le_right
  have : J.IsFiniteRelIndex S := ⟨fun h ↦ J.relIndex_ne_zero
    (by rw [← Subgroup.relIndex_mul_relIndex J S K hJS hSK, h, zero_mul])⟩
  have h_sum : doubleCosetClassSum Γ J f = J.relIndex S • doubleCosetClassSum Γ S f :=
    doubleCosetClassSum_eq_relIndex_smul_of_le hl
      (fun k hk ↦ mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 hk).1) hJS
  rw [h_sum, classIntegral_def, ← Subgroup.relIndex_mul_relIndex J S K hJS hSK,
    inv_natCast_mul_smul_nsmul Subgroup.relIndex_ne_zero]

/-- If `K` fixes `f`, the class integral is the class sum. -/
theorem classIntegral_eq_doubleCosetClassSum {f : G → W} (hK : K ≤ rightTranslationStabilizer f) :
    classIntegral Γ K f = doubleCosetClassSum Γ K f := by
  simp [classIntegral_def, inf_eq_right.2 hK]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The class integral is additive** on left `Γ`-invariant functions with open stabilisers, for
`(Γ, K)` of finite type. -/
theorem classIntegral_add (hK : HasFiniteType Γ K) {f f' : G → W}
    (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (hl' : ∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g)
    (hf : IsOpen (rightTranslationStabilizer f : Set G))
    (hf' : IsOpen (rightTranslationStabilizer f' : Set G)) :
    classIntegral Γ K (f + f') = classIntegral Γ K f + classIntegral Γ K f' := by
  -- Compute all three at the open level `J = Stab f ∩ Stab f' ∩ K`.
  set J := rightTranslationStabilizer f ⊓ rightTranslationStabilizer f' ⊓ K
  have hJK : J ≤ K := inf_le_right
  have hJf : J ≤ rightTranslationStabilizer f := inf_le_left.trans inf_le_left
  have hJf' : J ≤ rightTranslationStabilizer f' := inf_le_left.trans inf_le_right
  have : J.IsFiniteRelIndex K :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact ((hf.inter hf').inter hK.isOpen)
      hK.isCompact
  have := hK.finite_doubleCoset
  have := finite_doubleCoset_of_le (Γ := Γ) hJK
  rw [classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum
      (fun γ hγ g ↦ by simp [hl γ hγ, hl' γ hγ]) hJK
      (fun k hk ↦ mem_rightTranslationStabilizer.2 fun g ↦ by
        simp [mem_rightTranslationStabilizer.1 (hJf hk) g,
          mem_rightTranslationStabilizer.1 (hJf' hk) g]),
    classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum hl hJK hJf,
    classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum hl' hJK hJf', doubleCosetClassSum_add,
    smul_add]

/-- **Additive maps commute with the class integral**, for `(Γ, K)` of finite type and `f` with open
stabiliser. -/
theorem map_classIntegral (hK : HasFiniteType Γ K) (φ : W →+ W') {f : G → W}
    (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (hf : IsOpen (rightTranslationStabilizer f : Set G)) :
    φ (classIntegral Γ K f) = classIntegral Γ K (φ ∘ f) := by
  have : (rightTranslationStabilizer f ⊓ K).IsFiniteRelIndex K :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact (hf.inter hK.isOpen) hK.isCompact
  have := hK.finite_doubleCoset
  have := finite_doubleCoset_of_le (Γ := Γ) (inf_le_right : rightTranslationStabilizer f ⊓ K ≤ K)
  rw [classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum (f := φ ∘ f)
      (J := rightTranslationStabilizer f ⊓ K) (fun γ hγ g ↦ by simp [hl γ hγ]) inf_le_right
      (fun k hk ↦ mem_rightTranslationStabilizer.2 fun g ↦ by
        simp [mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 hk).1 g]),
    classIntegral_def, map_rat_smul, map_doubleCosetClassSum]

omit [IsTopologicalGroup G] in
/-- For `(Γ, K)` of finite type and `M ⊂ K` with `b⁻¹ M b ⊂ K`, both of finite index,
`[K : M] = [K : b⁻¹ M b]`: both indices are `S_{Γ,M}(1) / S_{Γ,K}(1)`, the class set of `K` having
positive mass. -/
private theorem relIndex_eq_relIndex_conj (hK : HasFiniteType Γ K) {M : Subgroup G} (b : G)
    (hMK : M ≤ K) (hbM : MulAut.conj b⁻¹ • M ≤ K) [M.IsFiniteRelIndex K]
    [(MulAut.conj b⁻¹ • M).IsFiniteRelIndex K] :
    M.relIndex K = (MulAut.conj b⁻¹ • M).relIndex K := by
  have h₁ := doubleCosetClassSum_eq_relIndex_smul_of_le (Γ := Γ) (f := fun _ : G ↦ (1 : ℚ))
    (by simp) (by simp) hMK
  have h₂ := doubleCosetClassSum_comp_mul_right (Γ := Γ) (f := fun _ : G ↦ (1 : ℚ)) (by simp)
    (by simp) b hbM
  rw [h₁, doubleCosetClassSum_one, nsmul_eq_mul, nsmul_eq_mul] at h₂
  exact_mod_cast mul_right_cancel₀ hK.orbitMass_pos.ne' h₂

/-- **The class integral is invariant under right translation**: for `(Γ, K)` of finite type and
`f` left `Γ`-invariant with open stabiliser, `I_{Γ,K}(g ↦ f (g b)) = I_{Γ,K}(f)`. -/
theorem classIntegral_comp_mul_right (hK : HasFiniteType Γ K) {f : G → W}
    (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (hf : IsOpen (rightTranslationStabilizer f : Set G))
    (b : G) :
    classIntegral Γ K (fun g ↦ f (g * b)) = classIntegral Γ K f := by
  -- Compute at `J = Stab f ∩ K` and at `M = K ∩ b J b⁻¹`, which fixes `f (· b)`, with
  -- `b⁻¹ M b ⊂ J`; the indices match by `relIndex_eq_relIndex_conj`.
  set J := rightTranslationStabilizer f ⊓ K
  have hJK : J ≤ K := inf_le_right
  have hJ_open : IsOpen (J : Set G) := hf.inter hK.isOpen
  set M := K ⊓ MulAut.conj b • J
  have hM_open : IsOpen (M : Set G) :=
    hK.isOpen.inter ((Subgroup.isOpen_map_conj_iff b).2 hJ_open)
  have hbM_open : IsOpen ((MulAut.conj b⁻¹ • M : Subgroup G) : Set G) :=
    (Subgroup.isOpen_map_conj_iff b⁻¹).2 hM_open
  have hbM : MulAut.conj b⁻¹ • M ≤ J := fun x hx ↦ by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have := (Subgroup.mem_inf.1 hx).2
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [MulAut.smul_def, mul_assoc] using this
  have hJ_cpt : IsCompact (J : Set G) :=
    hK.isCompact.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hJ_open) hJK
  have : M.IsFiniteRelIndex K :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact hM_open hK.isCompact
  have : J.IsFiniteRelIndex K :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact hJ_open hK.isCompact
  have : (MulAut.conj b⁻¹ • M).IsFiniteRelIndex J :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact hbM_open hJ_cpt
  have : (MulAut.conj b⁻¹ • M).IsFiniteRelIndex K :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact hbM_open hK.isCompact
  have h_index := relIndex_eq_relIndex_conj hK b inf_le_left (hbM.trans hJK)
  rw [← Subgroup.relIndex_mul_relIndex _ J K hbM hJK] at h_index
  have hMf : M ≤ rightTranslationStabilizer fun g ↦ f (g * b) := fun k hk ↦
      mem_rightTranslationStabilizer.2 fun g ↦ by
        have h := (Subgroup.mem_inf.1 hk).2
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
        simpa [MulAut.smul_def, mul_assoc] using
          mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 h).1 (g * b)
  rw [classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum
      (fun γ hγ g ↦ by simp [mul_assoc, hl γ hγ]) inf_le_left hMf,
    doubleCosetClassSum_comp_mul_right hl
      (fun k hk g ↦ mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 hk).1 g) b hbM,
    classIntegral_eq_inv_relIndex_smul_doubleCosetClassSum hl hJK inf_le_left, h_index,
    inv_natCast_mul_smul_nsmul Subgroup.relIndex_ne_zero]

end ClassIntegral

end TauCeti
