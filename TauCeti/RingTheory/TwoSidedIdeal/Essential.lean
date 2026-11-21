/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Algebra.Module.Submodule.Essential
public import TauCeti.RingTheory.TwoSidedIdeal.Basic
public import TauCeti.RingTheory.TwoSidedIdeal.Kernel

/-!
# Essential two-sided ideals

Essential two-sided ideals (`TwoSidedIdeal.IsEssential`), lattice and `comap` API, bridges to
`TauCeti.IsEssential` on `I.asIdeal` / `I.asIdealOpposite`, and product-projection kernels.

## Main declarations

* `TwoSidedIdeal.IsEssential`, `TwoSidedIdeal.isEssential_inf_iff`,
  `TwoSidedIdeal.isEssential_bot_iff`, `TwoSidedIdeal.isEssential_comap_iff`.
* `TwoSidedIdeal.isEssential_of_isEssential_asIdeal`,
  `TwoSidedIdeal.isEssential_iff_isEssential_asIdeal`, `TwoSidedIdeal.isEssential_ker_snd_iff`.
-/

public section

namespace TwoSidedIdeal

section Essential

variable {A : Type*} [NonUnitalNonAssocRing A] {I J : TwoSidedIdeal A}

/-- A two-sided ideal is *essential* when it meets every nonzero two-sided ideal. -/
def IsEssential (I : TwoSidedIdeal A) : Prop :=
  ∀ J : TwoSidedIdeal A, Disjoint I J → J = ⊥

theorem isEssential_iff : I.IsEssential ↔ ∀ J : TwoSidedIdeal A, Disjoint I J → J = ⊥ :=
  Iff.rfl

theorem isEssential_def : I.IsEssential ↔ ∀ J : TwoSidedIdeal A, J ≠ ⊥ → I ⊓ J ≠ ⊥ := by
  simp only [isEssential_iff, disjoint_iff]
  exact ⟨fun h J hJ hIJ => hJ (h J hIJ), fun h J hIJ => by_contra fun hJ => h J hJ hIJ⟩

theorem isEssential_iff_inf_eq_bot :
    I.IsEssential ↔ ∀ J : TwoSidedIdeal A, I ⊓ J = ⊥ → J = ⊥ := by
  simp only [isEssential_iff, disjoint_iff]

theorem IsEssential.eq_bot_of_disjoint (hI : I.IsEssential) (h : Disjoint I J) : J = ⊥ :=
  hI J h

theorem isEssential_top : (⊤ : TwoSidedIdeal A).IsEssential :=
  fun _ h ↦ disjoint_top.1 h.symm

theorem IsEssential.mono (hI : I.IsEssential) (h : I ≤ J) : J.IsEssential :=
  fun _ hK ↦ hI _ (hK.mono_left h)

theorem IsEssential.inf (hI : I.IsEssential) (hJ : J.IsEssential) : (I ⊓ J).IsEssential :=
  isEssential_iff_inf_eq_bot.mpr fun K hIJK =>
    isEssential_iff_inf_eq_bot.mp hJ K <|
      isEssential_iff_inf_eq_bot.mp hI (J ⊓ K) (by rwa [← inf_assoc])

@[simp]
theorem isEssential_inf_iff : (I ⊓ J).IsEssential ↔ I.IsEssential ∧ J.IsEssential :=
  ⟨fun h => ⟨h.mono inf_le_left, h.mono inf_le_right⟩, fun ⟨hI, hJ⟩ => hI.inf hJ⟩

@[simp]
theorem isEssential_bot_iff : (⊥ : TwoSidedIdeal A).IsEssential ↔ Subsingleton A :=
  ⟨fun h => subsingleton_iff.mp <|
      subsingleton_iff_bot_eq_top.mp (isEssential_iff_inf_eq_bot.mp h ⊤ (by simp)).symm,
   fun _ => isEssential_iff_inf_eq_bot.mpr fun J _ => Subsingleton.elim J ⊥⟩

theorem not_isEssential_bot [Nontrivial A] : ¬ (⊥ : TwoSidedIdeal A).IsEssential := by
  rw [isEssential_bot_iff]
  exact not_subsingleton A

theorem IsEssential.ne_bot [Nontrivial A] (hI : I.IsEssential) : I ≠ ⊥ :=
  fun h => not_isEssential_bot (h ▸ hI)

/-- Pulling back along a ring equivalence preserves and reflects essentiality. -/
@[simp]
theorem isEssential_comap_iff {B E : Type*} [NonUnitalNonAssocRing B]
    [EquivLike E A B] [NonUnitalRingHomClass E A B] (e : E) {I : TwoSidedIdeal B} :
    (I.comap e).IsEssential ↔ I.IsEssential := by
  let e' : A ≃+* B := { EquivLike.toEquiv e with map_mul' := map_mul e, map_add' := map_add e }
  let φ := e'.mapTwoSidedIdeal.symm
  have hcomap : I.comap e = φ I := by
    ext a
    exact (mem_comap e).trans (mem_comap e').symm
  rw [hcomap, isEssential_iff_inf_eq_bot, isEssential_iff_inf_eq_bot]
  refine ⟨fun h J hIJ => (map_eq_bot_iff φ).mp (h (φ J) (by rw [← map_inf, hIJ, map_bot])),
    fun h K hIK => ?_⟩
  rw [← φ.apply_symm_apply K] at hIK ⊢
  rw [← map_inf, map_eq_bot_iff] at hIK
  rw [h (φ.symm K) hIK, map_bot]

end Essential

section Ring

variable {R : Type*} [Ring R]

/-- If `I.asIdeal` is essential as a left ideal (`TauCeti.IsEssential`), then `I` is essential as a
two-sided ideal. -/
theorem isEssential_of_isEssential_asIdeal {I : TwoSidedIdeal R}
    (hI : TauCeti.IsEssential I.asIdeal) : I.IsEssential :=
  isEssential_iff_inf_eq_bot.mpr fun J hIJ =>
    orderIsoIsTwoSided.injective <| Subtype.ext <|
      TauCeti.isEssential_iff.mp hI J.asIdeal (by rw [← gc.u_inf, hIJ, bot_asIdeal])

/-- If `I.asIdealOpposite` is essential as a right ideal (`TauCeti.IsEssential`), then `I` is
essential as a two-sided ideal. -/
theorem isEssential_of_isEssential_asIdealOpposite {I : TwoSidedIdeal R}
    (hI : TauCeti.IsEssential I.asIdealOpposite) : I.IsEssential := by
  refine isEssential_iff_inf_eq_bot.mpr fun J hIJ => ?_
  have hinf : I.asIdealOpposite ⊓ J.asIdealOpposite = ⊥ := by
    ext x
    rw [Submodule.mem_inf, mem_asIdealOpposite, mem_asIdealOpposite, Submodule.mem_bot]
    refine ⟨fun hx => MulOpposite.unop_injective ?_, fun hx => by simp [hx]⟩
    exact (mem_bot _).mp (hIJ ▸ (⟨hx.left, hx.right⟩ : x.unop ∈ I ⊓ J))
  have hJ : J.asIdealOpposite = ⊥ := TauCeti.isEssential_iff.mp hI J.asIdealOpposite hinf
  ext x
  have hx : MulOpposite.op x ∈ J.asIdealOpposite ↔ MulOpposite.op x ∈ (⊥ : Ideal Rᵐᵒᵖ) :=
    SetLike.ext_iff.mp hJ (MulOpposite.op x)
  simpa [mem_asIdealOpposite, Submodule.mem_bot, mem_bot] using hx

end Ring

section CommRing

/-- In a commutative ring, a two-sided ideal is essential if and only if its underlying ideal is
essential as an `R`-submodule. -/
theorem isEssential_iff_isEssential_asIdeal {R : Type*} [CommRing R] {I : TwoSidedIdeal R} :
    I.IsEssential ↔ TauCeti.IsEssential I.asIdeal :=
  ⟨fun hI => TauCeti.isEssential_iff.mpr fun K hIK => by
      have hK : Ideal.toTwoSided K = ⊥ := isEssential_iff_inf_eq_bot.mp hI (Ideal.toTwoSided K) <|
        orderIsoIsTwoSided.injective <| Subtype.ext <| by
          simp [gc.u_inf, hIK]
      simpa using congrArg asIdeal hK,
   isEssential_of_isEssential_asIdeal⟩

end CommRing

section Prod

/-- In a product `A × B`, the first-factor ideal `A × {0} = ker snd` is essential if and only if `B`
is a subsingleton. -/
@[simp]
theorem isEssential_ker_snd_iff {A B : Type*} [NonUnitalNonAssocRing A]
    [NonUnitalNonAssocRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).IsEssential ↔ Subsingleton B := by
  refine ⟨fun h => ker_fst_eq_bot_iff.mp (isEssential_iff_inf_eq_bot.mp h _ ker_snd_inf_ker_fst),
    fun _ => ?_⟩
  have htop : TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) = ⊤ := by
    ext p
    simp [mem_ker, NonUnitalRingHom.coe_snd, Subsingleton.elim p.snd 0]
  rw [htop]
  exact isEssential_top

/-- In a product `A × B`, the second-factor ideal `{0} × B = ker fst` is essential if and only if
`A` is a subsingleton. -/
@[simp]
theorem isEssential_ker_fst_iff {A B : Type*} [NonUnitalNonAssocRing A]
    [NonUnitalNonAssocRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).IsEssential ↔ Subsingleton A := by
  refine ⟨fun h => ker_snd_eq_bot_iff.mp (isEssential_iff_inf_eq_bot.mp h _ ker_fst_inf_ker_snd),
    fun _ => ?_⟩
  have htop : TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) = ⊤ := by
    ext p
    simp [mem_ker, NonUnitalRingHom.coe_fst, Subsingleton.elim p.fst 0]
  rw [htop]
  exact isEssential_top

@[simp]
theorem isEssential_ker_snd_nonUnitalStarAlgHom_iff {R A B : Type*} [Monoid R]
    [NonUnitalNonAssocRing A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocRing B] [DistribMulAction R B] [Star B] :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd R A B)).IsEssential ↔ Subsingleton B := by
  rw [ker_nonUnitalStarAlgHom_snd, isEssential_ker_snd_iff]

@[simp]
theorem isEssential_ker_fst_nonUnitalStarAlgHom_iff {R A B : Type*} [Monoid R]
    [NonUnitalNonAssocRing A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocRing B] [DistribMulAction R B] [Star B] :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst R A B)).IsEssential ↔ Subsingleton A := by
  rw [ker_nonUnitalStarAlgHom_fst, isEssential_ker_fst_iff]

end Prod

end TwoSidedIdeal
