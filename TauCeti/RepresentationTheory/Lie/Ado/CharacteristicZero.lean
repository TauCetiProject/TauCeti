/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.LeviDecomposition.Solvable
public import TauCeti.Algebra.Lie.Prod
public import TauCeti.RepresentationTheory.Lie.Abelian
public import TauCeti.RepresentationTheory.Lie.EnvelopingExtension.Nilrepresentation
import TauCeti.LinearAlgebra.End.Prod

/-!
# Ado's theorem in characteristic zero

Every finite-dimensional Lie algebra `L` over a field of characteristic zero has a faithful
finite-dimensional representation, and one can be chosen in which every element of the nilradical
`N` acts nilpotently.

## The argument

Following Fulton–Harris, a representation that is faithful on the centre `Z` of `L` is grown along
a chain of Lie subalgebras

`Z = S₀ ⊂ S₁ ⊂ ⋯ ⊂ N ⊂ ⋯ ⊂ R ⊂ L`,

where `R` is the solvable radical. Each step `S ⊂ S'` exhibits `S'` as a split extension of `S` by
a complementary subalgebra `H` whose adjoint action on `S` takes values in `N`, and
`TauCeti.exists_semiDirectSum_rep_of_forall_mem` extends the representation across it, without
losing any direction of `S` that was detected and keeping the elements of `N` nilpotent.

* From `Z` to `N` the steps have codimension one. A proper subspace of the nilpotent ideal `N`
  is normalized by a further element of `N` (`LieIdeal.exists_mem_notMem_lie_mem_of_lt`), and
  every element of `N` is `ad`-nilpotent, so the extended representation stays nilpotent on the
  whole of the larger algebra.
* From `N` to `R` the steps again have codimension one: `⁅L, R⁆ ≤ N`
  (`TauCeti.LieAlgebra.lie_radical_le_nilradical`) makes every subspace between `N` and `R` an
  ideal of `L`.
* From `R` to `L` the complement is a Levi subalgebra (`TauCeti.exists_leviComplement`), whose
  adjoint action on `R` again lands in `N`.

The resulting representation `ρ₀` of `L` is faithful on `Z`, and the adjoint representation has
kernel exactly `Z`, so `ρ₀ ⊕ ad` is faithful.

## Main results

* `TauCeti.exists_faithful_nilrepresentation_charZero`: a faithful finite-dimensional
  representation in which every element of the nilradical acts nilpotently.
* `TauCeti.adoCharZero`: **Ado's theorem in characteristic zero.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2.
* S. Asgarli, [*Ado's Theorem*](https://personal.math.ubc.ca/~reichst/Ado%27s-Theorem.pdf).
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter VI.
-/

public section

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

variable (K L) in
/-- A Lie subalgebra `T` of `L` is an *Ado stage* when some finite-dimensional representation of
`T` kills no nonzero central element of `L` and lets every element of the nilradical of `L` that
lies in `T` act nilpotently. -/
private def IsAdoStage (T : LieSubalgebra K L) : Prop :=
  ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
    (σ : T →ₗ⁅K⁆ Module.End K V),
    (∀ z : T, (z : L) ∈ LieAlgebra.center K L → σ z = 0 → z = 0) ∧
      ∀ z : T, (z : L) ∈ LieAlgebra.nilradical K L → IsNilpotent (σ z)

/-- The centre of `L` is an Ado stage: it is abelian, so its square-zero representation is
faithful and nilpotent. -/
private theorem isAdoStage_center : IsAdoStage K L (LieAlgebra.center K L).toLieSubalgebra := by
  have : IsLieAbelian (LieAlgebra.center K L).toLieSubalgebra :=
    inferInstanceAs (IsLieAbelian (LieAlgebra.center K L))
  obtain ⟨V, _, _, _, σ, hσ, hsq, -⟩ :=
    exists_faithful_squareZeroRepresentation K (LieAlgebra.center K L).toLieSubalgebra
  exact ⟨V, inferInstance, inferInstance, inferInstance, σ,
    fun z _ hz ↦ hσ (hz.trans σ.map_zero.symm), fun z _ ↦ ⟨2, by rw [pow_two, hsq]⟩⟩

/-- **One step of the Ado flag.** Let `T'` be the sum of a Lie subalgebra `T` and a complementary
Lie subalgebra `H` that normalizes `T` with brackets in the nilradical `N`. If `T` contains the
centre and either contains `N` or `T'` lies inside `N`, then an Ado stage at `T` extends to one at
`T'`. -/
private theorem isAdoStage_of_sup {T T' H : LieSubalgebra K L}
    (hsup : T.toSubmodule ⊔ H.toSubmodule = T'.toSubmodule)
    (hdisj : Disjoint T.toSubmodule H.toSubmodule)
    (hHT : ∀ h ∈ H, ∀ t ∈ T, ⁅h, t⁆ ∈ T ∧ ⁅h, t⁆ ∈ LieAlgebra.nilradical K L)
    (hZ : ∀ z ∈ LieAlgebra.center K L, z ∈ T)
    (hN : (∀ z ∈ LieAlgebra.nilradical K L, z ∈ T) ∨ ∀ z ∈ T', z ∈ LieAlgebra.nilradical K L)
    (hT : IsAdoStage K L T) : IsAdoStage K L T' := by
  -- Read `T` as an ideal `I` of `T'` complemented by `H`, so that `T' ≃ I ⋊ H`; extend the
  -- representation of `T` across that split extension, and check the two Ado-stage conditions on
  -- `T'`: the centre lies in `I`, and the nilradical either lies in `I` or contains all of `T'`.
  obtain ⟨V, _, _, _, σ, hσZ, hσN⟩ := hT
  have hmemsup {y : L} (hy : y ∈ T') : y ∈ T.toSubmodule ⊔ H.toSubmodule := by
    rw [hsup]
    exact hy
  have hTT' : ∀ t ∈ T, t ∈ T' := fun t ht ↦ by
    rw [← LieSubalgebra.mem_toSubmodule, ← hsup]
    exact Submodule.mem_sup_left ht
  have hHT' : ∀ h ∈ H, h ∈ T' := fun h hh ↦ by
    rw [← LieSubalgebra.mem_toSubmodule, ← hsup]
    exact Submodule.mem_sup_right hh
  -- `T`, read inside `T'`, is an ideal of `T'` complemented by `H`.
  let I : LieIdeal K T' :=
    { T.toSubmodule.comap T'.toSubmodule.subtype with
      lie_mem := fun {x m} hm ↦ by
        obtain ⟨t, ht, h, hh, hx⟩ := Submodule.mem_sup.mp (hmemsup x.2)
        -- membership in the comap is membership of the underlying element of `L` in `T`
        change ⁅(x : L), (m : L)⁆ ∈ T
        rw [← hx, add_lie]
        exact T.add_mem (T.lie_mem ht hm) (hHT h hh _ hm).1 }
  have hmemI {x : T'} : x ∈ I ↔ (x : L) ∈ T := Iff.rfl
  let H' : LieSubalgebra K T' := H.comap T'.incl
  have hc : IsCompl I.toSubmodule H'.toSubmodule := by
    refine ⟨Submodule.disjoint_def.mpr fun x hxI hxH ↦ Subtype.ext ?_,
      codisjoint_iff.mpr (Submodule.eq_top_iff'.mpr fun x ↦ ?_)⟩
    · exact (Submodule.disjoint_def.mp hdisj) _ hxI hxH
    · obtain ⟨t, ht, h, hh, hx⟩ := Submodule.mem_sup.mp (hmemsup x.2)
      refine Submodule.mem_sup.mpr ⟨⟨t, hTT' t ht⟩, ht, ⟨h, hHT' h hh⟩, hh, Subtype.ext hx⟩
  let e := I.semiDirectSumEquiv H' hc
  let ψ := (LieIdeal.ad I).comp H'.incl
  -- The representation `σ` of `T`, read on the ideal `I` of `T'`.
  let ι : I →ₗ⁅K⁆ T :=
    { toFun := fun y ↦ ⟨((y : T') : L), y.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := fun {_ _} ↦ rfl }
  let NI : LieIdeal K I := (LieAlgebra.nilradical K L).comap (T'.incl.comp I.incl)
  have hNI {y : I} : y ∈ NI ↔ ((y : T') : L) ∈ LieAlgebra.nilradical K L := Iff.rfl
  have hψ (h : H') (s : I) : (((ψ h s : I) : T') : L) = ⁅((h : T') : L), ((s : T') : L)⁆ := by
    simp only [ψ, LieHom.coe_comp, Function.comp_apply, LieIdeal.ad_apply_apply]
    rfl
  obtain ⟨W, _, _, _, ρ, hker, hiff, hall⟩ := exists_semiDirectSum_rep_of_forall_mem ψ NI
    (σ.comp ι) (fun s hs ↦ hσN _ (hNI.mp hs))
    fun h s ↦ hNI.mpr (by rw [hψ]; exact (hHT _ h.2 _ s.2).2)
  have he (z : T') (hz : (z : L) ∈ T) :
      e.symm z = LieAlgebra.SemiDirectSum.inl ψ ⟨z, hmemI.mpr hz⟩ :=
    LieIdeal.semiDirectSumEquiv_symm_of_mem_left I H' hc (hmemI.mpr hz)
  refine ⟨W, inferInstance, inferInstance, inferInstance, ρ.comp e.symm.toLieHom,
    fun z hzZ hz ↦ ?_, fun z hzN ↦ ?_⟩
  · have hzT := hZ _ hzZ
    have hmem : (⟨z, hmemI.mpr hzT⟩ : I) ∈ (ρ.comp (LieAlgebra.SemiDirectSum.inl ψ)).ker := by
      rw [LieHom.mem_ker, LieHom.comp_apply, ← he z hzT]
      exact hz
    have h0 := congrArg (fun w : T ↦ (w : L))
      (hσZ (ι ⟨z, hmemI.mpr hzT⟩) hzZ (LieHom.mem_ker.mp (hker hmem)))
    exact Subtype.ext h0
  · rcases hN with hN | hN
    · have hzT := hN _ hzN
      rw [LieHom.comp_apply, LieEquiv.coe_toLieHom, he z hzT, hiff]
      exact hσN _ hzN
    · -- every component in `H` is `ad`-nilpotent, so its derivation of `I` is nilpotent
      have hloc (r : H') (s : I) : ∃ n : ℕ, ((ψ r).toLinearMap ^ n) s = 0 := by
        obtain ⟨n, hn⟩ : IsNilpotent (LieAlgebra.ad K L ((r : T') : L)) :=
          LieAlgebra.isNilpotent_ad_of_mem_nilradical (hN _ (hHT' _ r.2))
        -- `ψ r` is intertwined with `ad r` by the inclusion `I → L`, hence so are their powers
        let f : I →ₗ[K] L := T'.incl.toLinearMap ∘ₗ I.incl.toLinearMap
        have hf : (LieAlgebra.ad K L ((r : T') : L)).comp f = f.comp (ψ r).toLinearMap :=
          LinearMap.ext fun s ↦ (hψ r s).symm
        refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
        have hpow := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hf n) s
        rw [hn, LinearMap.zero_comp] at hpow
        exact hpow.symm
      exact hall (fun s ↦ hσN _ (hN _ (hTT' _ (ι s).2))) _ fun s ↦ hloc _ s

/-- **A codimension-one step of the Ado flag.** An Ado stage at `T` extends to the Lie span
`K ∙ x ⊔ T` of `x` and `T`, for an element `x ∉ T` whose brackets with `T` lie in `T ⊓ N`, provided
`T` contains the centre and either `T` contains `N` or both `x` and `T` lie in `N`. -/
private theorem isAdoStage_lieSpan_insert (T : LieSubalgebra K L) {x : L} (hx : x ∈ T.normalizer)
    (hxN : ∀ t ∈ T, ⁅x, t⁆ ∈ LieAlgebra.nilradical K L)
    (hxT : x ∉ T) (hZ : ∀ z ∈ LieAlgebra.center K L, z ∈ T)
    (hN : (∀ z ∈ LieAlgebra.nilradical K L, z ∈ T) ∨
      (x ∈ LieAlgebra.nilradical K L ∧ ∀ z ∈ T, z ∈ LieAlgebra.nilradical K L))
    (hT : IsAdoStage K L T) :
    IsAdoStage K L (LieSubalgebra.lieSpan K L (insert x (T : Set L))) := by
  have hH : (LieSubalgebra.lieSpan K L {x}).toSubmodule = K ∙ x :=
    LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (by simp)
  refine isAdoStage_of_sup (H := LieSubalgebra.lieSpan K L {x})
    (by rw [LieSubalgebra.lieSpan_insert_toSubmodule T hx, hH, sup_comm])
    (hH ▸ Submodule.disjoint_span_singleton_of_notMem hxT) (fun h hh t ht ↦ ?_) hZ ?_ hT
  · rw [← LieSubalgebra.mem_toSubmodule, hH] at hh
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hh
    rw [smul_lie]
    exact ⟨T.smul_mem a (LieSubalgebra.ideal_in_normalizer hx ht),
      (LieAlgebra.nilradical K L).smul_mem a (hxN t ht)⟩
  · refine hN.imp_right fun ⟨hxN', hTN⟩ z hz ↦ ?_
    obtain ⟨a, t, ht, rfl⟩ := (T.mem_lieSpan_insert_iff hx).mp hz
    exact add_mem ((LieAlgebra.nilradical K L).smul_mem a hxN') (hTN t ht)

/-- **Climbing a flag.** If every Ado stage `T` satisfying `P` and strictly below `U` is followed
by a strictly larger Ado stage below `U` that again satisfies `P`, then an Ado stage satisfying `P`
below `U` gives one at `U`. -/
private theorem isAdoStage_of_forall_ne (U : LieSubalgebra K L) (P : LieSubalgebra K L → Prop)
    (hstep : ∀ T, P T → T ≤ U → T ≠ U → IsAdoStage K L T →
      ∃ T', P T' ∧ T < T' ∧ T' ≤ U ∧ IsAdoStage K L T')
    (T : LieSubalgebra K L) (hPT : P T) (hTU : T ≤ U) (hT : IsAdoStage K L T) :
    IsAdoStage K L U := by
  induction hn : Module.finrank K L - Module.finrank K T.toSubmodule
    using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    by_cases hTU' : T = U
    · exact hTU' ▸ hT
    obtain ⟨T', hPT', hlt, hT'U, hT'⟩ := hstep T hPT hTU hTU' hT
    have hlt' : T.toSubmodule < T'.toSubmodule :=
      lt_of_le_of_ne ((LieSubalgebra.toSubmodule_le_toSubmodule _ _).mpr hlt.le)
        fun h ↦ hlt.ne (LieSubalgebra.toSubmodule_injective h)
    have := Submodule.finrank_lt_finrank_of_lt hlt'
    have := Submodule.finrank_le T'.toSubmodule
    exact ih _ (by omega) T' hPT' hT'U hT' rfl

/-- The nilradical is an Ado stage, by a flag of codimension-one steps from the centre inside the
nilradical. -/
private theorem isAdoStage_nilradical :
    IsAdoStage K L (LieAlgebra.nilradical K L).toLieSubalgebra := by
  refine isAdoStage_of_forall_ne _ (fun T ↦ ∀ z ∈ LieAlgebra.center K L, z ∈ T)
    (fun T hZ hTN hne hT ↦ ?_) _ (fun _ ↦ id)
    (fun z hz ↦ (LieIdeal.mem_toLieSubalgebra K L _ _).mpr (LieAlgebra.center_le_nilradical K L hz))
    isAdoStage_center
  have hTN' : ∀ t ∈ T, t ∈ LieAlgebra.nilradical K L := fun t ht ↦
    (LieIdeal.mem_toLieSubalgebra K L _ _).mp (hTN ht)
  have hlt : T.toSubmodule < (LieAlgebra.nilradical K L).toSubmodule :=
    lt_of_le_of_ne (fun t ht ↦ hTN' t ht) fun h ↦ hne (LieSubalgebra.toSubmodule_injective
      (h.trans (LieIdeal.toLieSubalgebra_toSubmodule K L _).symm))
  obtain ⟨x, hxN, hxT, hx⟩ := (LieAlgebra.nilradical K L).exists_mem_notMem_lie_mem_of_lt hlt
  have hxnorm : x ∈ T.normalizer := (T.mem_normalizer_iff x).mpr fun t ht ↦ hx t (hTN' t ht)
  refine ⟨_, fun z hz ↦ LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ (hZ z hz)),
    T.lt_lieSpan_insert hxT, fun w hw ↦ ?_, isAdoStage_lieSpan_insert T hxnorm
      (fun t ht ↦ (LieAlgebra.nilradical K L).lie_mem (hTN' t ht)) hxT hZ (Or.inr ⟨hxN, hTN'⟩) hT⟩
  obtain ⟨a, t, ht, rfl⟩ := (T.mem_lieSpan_insert_iff hxnorm).mp hw
  exact (LieIdeal.mem_toLieSubalgebra K L _ _).mpr
    (add_mem ((LieAlgebra.nilradical K L).smul_mem a hxN) (hTN' t ht))

variable [CharZero K]

/-- In characteristic zero, every bracket with an element of the radical lies in the nilradical. -/
private theorem lie_mem_nilradical_of_mem_radical (x : L) {r : L}
    (hr : r ∈ LieAlgebra.radical K L) : ⁅x, r⁆ ∈ LieAlgebra.nilradical K L :=
  LieAlgebra.lie_radical_le_nilradical K L (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hr)

/-- The radical is an Ado stage, by a flag of codimension-one steps from the nilradical: every
subspace between the nilradical and the radical is an ideal. -/
private theorem isAdoStage_radical : IsAdoStage K L (LieAlgebra.radical K L).toLieSubalgebra := by
  refine isAdoStage_of_forall_ne _ (fun T ↦ ∀ z ∈ LieAlgebra.nilradical K L, z ∈ T)
    (fun T hNT hTR hne hT ↦ ?_) _ (fun _ ↦ id)
    (fun z hz ↦ (LieIdeal.mem_toLieSubalgebra K L _ _).mpr
      (LieAlgebra.nilradical_le_radical K L hz))
    isAdoStage_nilradical
  have hTR' : ∀ t ∈ T, t ∈ LieAlgebra.radical K L := fun t ht ↦
    (LieIdeal.mem_toLieSubalgebra K L _ _).mp (hTR ht)
  obtain ⟨x, hxR, hxT⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hTR hne)
  have hxR' : x ∈ LieAlgebra.radical K L := (LieIdeal.mem_toLieSubalgebra K L _ _).mp hxR
  have hxnorm : x ∈ T.normalizer := (T.mem_normalizer_iff x).mpr fun t ht ↦
    hNT _ (lie_mem_nilradical_of_mem_radical x (hTR' t ht))
  refine ⟨_, fun z hz ↦ LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ (hNT z hz)),
    T.lt_lieSpan_insert hxT, fun w hw ↦ ?_, isAdoStage_lieSpan_insert T hxnorm
      (fun t ht ↦ lie_mem_nilradical_of_mem_radical x (hTR' t ht)) hxT
      (fun z hz ↦ hNT z (LieAlgebra.center_le_nilradical K L hz)) (Or.inl hNT) hT⟩
  obtain ⟨a, t, ht, rfl⟩ := (T.mem_lieSpan_insert_iff hxnorm).mp hw
  exact (LieIdeal.mem_toLieSubalgebra K L _ _).mpr
    (add_mem ((LieAlgebra.radical K L).smul_mem a hxR') (hTR' t ht))

/-- The whole of `L` is an Ado stage, by extending from the radical across a Levi complement. -/
private theorem isAdoStage_top : IsAdoStage K L ⊤ := by
  obtain ⟨S, hS⟩ := exists_leviComplement K L
  exact isAdoStage_of_sup (T := (LieAlgebra.radical K L).toLieSubalgebra) (H := S)
    (by rw [LieIdeal.toLieSubalgebra_toSubmodule, hS.sup_eq_top, LieSubalgebra.top_toSubmodule])
    (by rw [LieIdeal.toLieSubalgebra_toSubmodule]; exact hS.disjoint)
    (fun s _ r hr ↦ ⟨(LieIdeal.mem_toLieSubalgebra K L _ _).mpr
        ((LieAlgebra.radical K L).lie_mem ((LieIdeal.mem_toLieSubalgebra K L _ _).mp hr)),
      lie_mem_nilradical_of_mem_radical s ((LieIdeal.mem_toLieSubalgebra K L _ _).mp hr)⟩)
    (fun z hz ↦ (LieIdeal.mem_toLieSubalgebra K L _ _).mpr (LieAlgebra.nilradical_le_radical K L
      (LieAlgebra.center_le_nilradical K L hz)))
    (Or.inl fun z hz ↦ (LieIdeal.mem_toLieSubalgebra K L _ _).mpr
      (LieAlgebra.nilradical_le_radical K L hz))
    isAdoStage_radical

variable (K L)

/-- **Ado's theorem in characteristic zero, with nilpotence on the nilradical.** A
finite-dimensional Lie algebra over a field of characteristic zero has a faithful
finite-dimensional representation in which every element of the nilradical acts nilpotently. -/
theorem exists_faithful_nilrepresentation_charZero :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (ρ : L →ₗ⁅K⁆ Module.End K V),
      Function.Injective ρ ∧ ∀ x ∈ LieAlgebra.nilradical K L, IsNilpotent (ρ x) := by
  obtain ⟨V, _, _, _, σ, hσZ, hσN⟩ := isAdoStage_top (K := K) (L := L)
  -- `ρ₀` is faithful on the centre and `ad` has kernel the centre, so their product is faithful.
  let ρ₀ := σ.comp (LieSubalgebra.topEquiv (R := K) (L := L)).symm.toLieHom
  have hρ₀ (x : L) : ρ₀ x = σ ⟨x, LieSubalgebra.mem_top x⟩ := rfl
  refine ⟨V × L, inferInstance, inferInstance, inferInstance,
    ρ₀.prodRepresentation (LieAlgebra.ad K L), ?_, fun x hx ↦ ?_⟩
  · rw [LieHom.prodRepresentation_injective_iff, disjoint_iff, eq_bot_iff]
    intro x hx
    rw [LieSubmodule.mem_inf, LieAlgebra.ad_ker_eq_self_module_ker,
      LieAlgebra.self_module_ker_eq_center] at hx
    obtain ⟨hx, hxZ⟩ := hx
    rw [LieSubmodule.mem_bot]
    rw [LieHom.mem_ker, hρ₀] at hx
    exact congrArg Subtype.val (hσZ _ hxZ hx)
  · have hprod : ρ₀.prodRepresentation (LieAlgebra.ad K L) x =
        (ρ₀ x).prodMap (LieAlgebra.ad K L x) :=
      LinearMap.ext fun p ↦ LieHom.prodRepresentation_apply _ _ x p
    rw [hprod, hρ₀]
    exact (hσN _ hx).prodMap (LieAlgebra.isNilpotent_ad_of_mem_nilradical hx)

/-- **Ado's theorem in characteristic zero.** Every finite-dimensional Lie algebra over a field of
characteristic zero admits a faithful finite-dimensional representation. -/
theorem adoCharZero :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ := by
  obtain ⟨V, _, _, _, ρ, hρ, -⟩ := exists_faithful_nilrepresentation_charZero K L
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hρ⟩

end TauCeti
