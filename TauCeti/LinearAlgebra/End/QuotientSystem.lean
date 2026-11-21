/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Finite quotient systems adapted to an endomorphism

Let `U` be an endomorphism of an `R`-module `M`. A *finite quotient system* for `(M, U)` is a
downward directed family `(J i)` of `U`-stable submodules of `M` with finite quotients `M ⧸ J i`,
such that `M` is separated (`⨅ i, J i = ⊥`) and complete (every compatible family of residues
`x i mod J i` comes from one element of `M`) for it. Equivalently, `M` is the inverse limit of the
finite modules `M ⧸ J i`, each carrying the endomorphism induced by `U`.

These are the data on which Hida's ordinary projector of a profinite module is built: on each
finite quotient `M ⧸ J i` the factorial powers of the induced endomorphism stabilise, and the
resulting finite projectors are compatible along the system, so they glue to an endomorphism of
`M`. The data are the submodules `J i`, not merely a topology: maps between modules with such
systems have to respect them.

## Main definitions

* `Module.End.FiniteQuotientSystem U ι`: a finite quotient system for `(M, U)` indexed by `ι`.
* `Module.End.FiniteQuotientSystem.mapQ`: the endomorphism of `M ⧸ J i` induced by `U`.
* `Module.End.FiniteQuotientSystem.limit`: the inverse limit `lim_i M ⧸ J i`, as the submodule of
  compatible families in `Π i, M ⧸ J i`.
* `Module.End.FiniteQuotientSystem.limitEquiv`: the isomorphism `M ≃ lim_i M ⧸ J i`.
* `Module.End.FiniteQuotientSystem.topology`: the inverse-limit topology on `M`, induced by the
  maps to the discrete quotients `M ⧸ J i`.
* `Module.End.FiniteQuotientSystem.ofIsAdicComplete`: the `I`-adic filtration `I ^ n • ⊤` of an
  `I`-adically complete module with finite quotients, and `ofModuleFinite` for a finite module
  over a ring with `R ⧸ I` finite and `I` finitely generated.
* `Module.End.FiniteQuotientSystem.ofFinite`: the one-term system `J = ⊥` on a module that is
  finite as a set.

## Main results

* `Module.End.FiniteQuotientSystem.eq_iff_forall_sModEq`: two elements agree if and only if they
  agree modulo every `J i`.
* `Module.End.FiniteQuotientSystem.existsUnique_sModEq`: every compatible family of residues has a
  unique limit.
* `Module.End.FiniteQuotientSystem.hasBasis_nhds_zero`: the submodules `J i` form a basis of
  neighbourhoods of `0` for the inverse-limit topology.
* `Module.End.FiniteQuotientSystem.isClosedEmbedding_pi`: `M` embeds as a closed subset of the
  product of its discrete quotients.
* `Module.End.FiniteQuotientSystem.compactSpace`, `Module.End.FiniteQuotientSystem.t2Space`: `M` is
  compact and Hausdorff for the inverse-limit topology.
* `Module.End.FiniteQuotientSystem.continuous`: `U` is continuous for it; more generally a linear
  map respecting two systems is continuous (`continuous_of_forall_exists_le_comap`).
* `Module.End.FiniteQuotientSystem.isEmpty_of_infinite`: a nonzero module over an infinite
  division ring has no finite quotient system.

## References

* H. Hida, *Iwasawa modules attached to congruences of cusp forms*, Ann. Sci. ÉNS (4) 19 (1986),
  §1, (1.17b).
* C. Khare and J. Thorne, *Potential automorphy and the Leopoldt conjecture*, Amer. J. Math. 139
  (2017), §2.4, proof of Lemma 2.10.
-/

public section

open Filter Submodule Topology

namespace Module.End

variable {R M : Type*} [AddCommGroup M]

section Ring

variable [Ring R] [Module R M]

/-- A *finite quotient system* for an endomorphism `U` of `M`, indexed by `ι`: a downward directed
family of `U`-stable submodules `J i` with finite quotients `M ⧸ J i`, for which `M` is separated
and complete, so that `M` is the inverse limit of the finite modules `M ⧸ J i`. -/
@[ext]
structure FiniteQuotientSystem (U : Module.End R M) (ι : Type*) where
  /-- The submodules `J i` of the system. -/
  submodule : ι → Submodule R M
  /-- Any two members of the system contain a third. -/
  directed : Directed (· ≥ ·) submodule
  /-- Each `J i` is stable under `U`. -/
  le_comap : ∀ i, submodule i ≤ (submodule i).comap U
  /-- Each quotient `M ⧸ J i` is finite. -/
  finite_quotient : ∀ i, _root_.Finite (M ⧸ submodule i)
  /-- Separation: the `J i` have zero intersection. -/
  iInf_eq_bot : ⨅ i, submodule i = ⊥
  /-- Completeness: every compatible family of residues is represented by one element. -/
  exists_sModEq : ∀ x : ι → M, (∀ i j, submodule i ≤ submodule j → x i ≡ x j [SMOD submodule j]) →
    ∃ y, ∀ i, x i ≡ y [SMOD submodule i]

namespace FiniteQuotientSystem

variable {U : Module.End R M} {ι : Type*} (h : U.FiniteQuotientSystem ι)

instance (i : ι) : _root_.Finite (M ⧸ h.submodule i) := h.finite_quotient i

/-- Two elements agree if and only if they agree modulo every member of the system. -/
theorem eq_iff_forall_sModEq {x y : M} : x = y ↔ ∀ i, x ≡ y [SMOD h.submodule i] := by
  refine ⟨fun hxy _ ↦ hxy ▸ SModEq.rfl, fun hxy ↦ ?_⟩
  rw [← sub_eq_zero, ← mem_bot R, ← h.iInf_eq_bot, Submodule.mem_iInf]
  exact fun i ↦ SModEq.sub_mem.1 (hxy i)

/-- Every compatible family of residues has a unique limit. -/
theorem existsUnique_sModEq (x : ι → M)
    (hx : ∀ i j, h.submodule i ≤ h.submodule j → x i ≡ x j [SMOD h.submodule j]) :
    ∃! y, ∀ i, x i ≡ y [SMOD h.submodule i] := by
  obtain ⟨y, hy⟩ := h.exists_sModEq x hx
  exact ⟨y, hy, fun z hz ↦ h.eq_iff_forall_sModEq.2 fun i ↦ (hz i).symm.trans (hy i)⟩

/-- The endomorphism of the finite quotient `M ⧸ J i` induced by `U`. -/
def mapQ (i : ι) : Module.End R (M ⧸ h.submodule i) :=
  (h.submodule i).mapQ (h.submodule i) U (h.le_comap i)

@[simp]
theorem mapQ_mk (i : ι) (x : M) :
    h.mapQ i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (U x) :=
  mapQ_apply _ _ _ x

@[simp]
theorem mapQ_pow_mk (i : ι) (n : ℕ) (x : M) :
    (h.mapQ i ^ n) (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((U ^ n) x) := by
  rw [mapQ, ← Submodule.mapQ_pow]
  exact mapQ_apply _ _ _ x

/-- The transition map `M ⧸ J i → M ⧸ J j` intertwines the induced endomorphisms. -/
theorem factor_mapQ {i j : ι} (hij : h.submodule i ≤ h.submodule j) (z : M ⧸ h.submodule i) :
    factor hij (h.mapQ i z) = h.mapQ j (factor hij z) := by
  induction z using Submodule.Quotient.induction_on with
  | H x => simp

/-- The inverse limit `lim_i M ⧸ J i`, realised as the submodule of `Π i, M ⧸ J i` of families
compatible with the transition maps `M ⧸ J i → M ⧸ J j` for `J i ≤ J j`. -/
def limit : Submodule R (Π i, M ⧸ h.submodule i) where
  carrier := {z | ∀ i j (hij : h.submodule i ≤ h.submodule j), factor hij (z i) = z j}
  add_mem' hz hw i j hij := by simp [hz i j hij, hw i j hij]
  zero_mem' := by simp
  smul_mem' c z hz i j hij := by simp [hz i j hij]

@[simp]
theorem mem_limit {z : Π i, M ⧸ h.submodule i} :
    z ∈ h.limit ↔ ∀ i j (hij : h.submodule i ≤ h.submodule j), factor hij (z i) = z j :=
  Iff.rfl

/-- The families of residues of elements of `M` are exactly the compatible families. -/
theorem range_mk_eq_limit :
    Set.range (fun x i ↦ (Submodule.Quotient.mk x : M ⧸ h.submodule i)) = h.limit := by
  ext z
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨x, rfl⟩ i j hij
    exact factor_mk hij x
  · choose x hx using fun i ↦ Submodule.Quotient.mk_surjective _ (z i)
    obtain ⟨y, hy⟩ := h.exists_sModEq x fun i j hij ↦ by
      rw [SModEq.def, hx j, ← hz i j hij, ← hx i]
      exact (factor_mk hij (x i)).symm
    exact ⟨y, funext fun i ↦ by rw [← hx i, ← SModEq.def]; exact (hy i).symm⟩

/-- The canonical map `M → lim_i M ⧸ J i`. -/
def toLimit : M →ₗ[R] h.limit :=
  (LinearMap.pi fun i ↦ (h.submodule i).mkQ).codRestrict h.limit fun x ↦
    h.range_mk_eq_limit.subset ⟨x, rfl⟩

@[simp]
theorem toLimit_apply_coe (x : M) (i : ι) : (h.toLimit x : Π i, M ⧸ h.submodule i) i =
    Submodule.Quotient.mk x :=
  (rfl)

/-- The canonical map to the inverse limit is bijective: injective by separation and surjective by
completeness. -/
theorem toLimit_bijective : Function.Bijective h.toLimit := by
  refine ⟨fun x y hxy ↦ h.eq_iff_forall_sModEq.2 fun i ↦ congr_fun (congr_arg Subtype.val hxy) i,
    fun z ↦ ?_⟩
  obtain ⟨x, hx⟩ := h.range_mk_eq_limit.superset z.property
  exact ⟨x, Subtype.ext hx⟩

/-- A module with a finite quotient system is the inverse limit of its finite quotients. -/
noncomputable def limitEquiv : M ≃ₗ[R] h.limit :=
  LinearEquiv.ofBijective h.toLimit h.toLimit_bijective

@[simp]
theorem limitEquiv_apply (x : M) : h.limitEquiv x = h.toLimit x :=
  (rfl)

@[simp]
theorem mk_limitEquiv_symm_apply (z : h.limit) (i : ι) :
    (Submodule.Quotient.mk (h.limitEquiv.symm z) : M ⧸ h.submodule i) =
      (z : Π i, M ⧸ h.submodule i) i := by
  rw [← toLimit_apply_coe, ← limitEquiv_apply, LinearEquiv.apply_symm_apply]

section Topology

/-- The inverse-limit topology on `M` defined by a finite quotient system: the coarsest topology
for which every quotient map `M → M ⧸ J i` is continuous, the quotients being discrete. -/
@[instance_reducible]
def topology : TopologicalSpace M :=
  ⨅ i, TopologicalSpace.induced (Submodule.Quotient.mk : M → M ⧸ h.submodule i) ⊥

/-- Each quotient map `M → M ⧸ J i` is continuous for the inverse-limit topology, the quotient
being discrete. -/
theorem continuous_mk (i : ι) :
    Continuous[h.topology, ⊥] (Submodule.Quotient.mk : M → M ⧸ h.submodule i) :=
  continuous_iInf_dom continuous_induced_dom

/-- Each member `J i` of the system is open for the inverse-limit topology. -/
theorem isOpen_submodule (i : ι) : IsOpen[h.topology] (h.submodule i : Set M) := by
  have hJ : (h.submodule i : Set M) = Submodule.Quotient.mk ⁻¹' {(0 : M ⧸ h.submodule i)} := by
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  rw [hJ]
  exact TopologicalSpace.le_def.1 (iInf_le _ i) _
    ((isOpen_induced_iff (t := ⊥)).2 ⟨_, trivial, rfl⟩)

/-- The inverse-limit topology is induced by the map `M → Π i, M ⧸ J i` to the product of the
discrete quotients. -/
theorem topology_eq_induced_pi :
    h.topology = TopologicalSpace.induced
      (fun x i ↦ (Submodule.Quotient.mk x : M ⧸ h.submodule i))
      (Pi.topologicalSpace (t₂ := fun _ ↦ ⊥)) := by
  simp only [topology, Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

/-- The neighbourhoods of `x` for the inverse-limit topology have a basis given by the residue
classes `x + J i`. -/
theorem hasBasis_nhds [Nonempty ι] (x : M) :
    (@nhds M h.topology x).HasBasis (fun _ ↦ True)
      fun i ↦ {y | y ≡ x [SMOD h.submodule i]} := by
  have hn : @nhds M h.topology x = ⨅ i, 𝓟 {y | y ≡ x [SMOD h.submodule i]} := by
    rw [topology, nhds_iInf]
    refine iInf_congr fun i ↦ ?_
    let _ : TopologicalSpace (M ⧸ h.submodule i) := ⊥
    have _ : DiscreteTopology (M ⧸ h.submodule i) := ⟨rfl⟩
    rw [nhds_induced, nhds_discrete, comap_pure]
    -- `y ≡ x [SMOD J]` is by definition `mk y = mk x`, so the two principal filters agree
    exact congrArg 𝓟 (Set.ext fun _ ↦ SModEq.def.symm)
  rw [hn]
  refine Filter.hasBasis_iInf_principal fun i j ↦ ?_
  obtain ⟨k, hki, hkj⟩ := h.directed i j
  exact ⟨k, fun _ hy ↦ SModEq.mono hki hy, fun _ hy ↦ SModEq.mono hkj hy⟩

/-- The members of a finite quotient system form a basis of neighbourhoods of `0` for the
inverse-limit topology. -/
theorem hasBasis_nhds_zero [Nonempty ι] :
    (@nhds M h.topology 0).HasBasis (fun _ ↦ True) fun i ↦ (h.submodule i : Set M) := by
  convert h.hasBasis_nhds 0 using 2 with i
  ext y
  exact SModEq.zero.symm

/-- A linear map between modules with finite quotient systems is continuous for the
inverse-limit topologies as soon as each member of the target system contains the image of some
member of the source system. -/
theorem continuous_of_forall_exists_le_comap {N : Type*} [AddCommGroup N] [Module R N]
    {V : Module.End R N} {κ : Type*} (h' : V.FiniteQuotientSystem κ) (f : M →ₗ[R] N)
    (hf : ∀ k, ∃ i, h.submodule i ≤ (h'.submodule k).comap f) :
    Continuous[h.topology, h'.topology] f := by
  refine continuous_iInf_rng.2 fun k ↦ continuous_induced_rng.2 ?_
  obtain ⟨i, hi⟩ := hf k
  have hfac : (Submodule.Quotient.mk ∘ f : M → N ⧸ h'.submodule k) =
      (h.submodule i).mapQ (h'.submodule k) f hi ∘ Submodule.Quotient.mk :=
    funext fun x ↦ (mapQ_apply _ _ _ x).symm
  -- a map factoring through the discrete quotient `M ⧸ J i` is continuous
  rw [hfac, continuous_iff_le_induced, ← induced_compose]
  exact (iInf_le _ i).trans (induced_mono bot_le)

/-- The endomorphism `U` is continuous for the inverse-limit topology. -/
protected theorem continuous : Continuous[h.topology, h.topology] U :=
  h.continuous_of_forall_exists_le_comap h U fun i ↦ ⟨i, h.le_comap i⟩

/-- The map `M → Π i, M ⧸ J i` to the product of the discrete quotients is a closed embedding
for the inverse-limit topology: its image is the closed subset of compatible families. -/
theorem isClosedEmbedding_pi :
    @IsClosedEmbedding M (Π i, M ⧸ h.submodule i) h.topology
      (Pi.topologicalSpace (t₂ := fun _ ↦ ⊥)) fun x _ ↦ Submodule.Quotient.mk x := by
  let _ : ∀ i, TopologicalSpace (M ⧸ h.submodule i) := fun _ ↦ ⊥
  have _ : ∀ i, DiscreteTopology (M ⧸ h.submodule i) := fun _ ↦ ⟨rfl⟩
  let _ := h.topology
  have hclosed : IsClosed (h.limit : Set (Π i, M ⧸ h.submodule i)) := by
    have hset : (h.limit : Set (Π i, M ⧸ h.submodule i)) =
        ⋂ i, ⋂ j, ⋂ hij : h.submodule i ≤ h.submodule j, {z | factor hij (z i) = z j} := by
      ext z
      simp
    rw [hset]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun hij ↦
      isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply i)) (continuous_apply j)
  refine ⟨⟨⟨h.topology_eq_induced_pi⟩, fun x y hxy ↦
    h.eq_iff_forall_sModEq.2 fun i ↦ congr_fun hxy i⟩, ?_⟩
  rw [h.range_mk_eq_limit]
  exact hclosed

/-- A module is compact for the inverse-limit topology of a finite quotient system: it embeds as
a closed subset of the compact product of its finite quotients. -/
theorem compactSpace : @CompactSpace M h.topology := by
  let _ : ∀ i, TopologicalSpace (M ⧸ h.submodule i) := fun _ ↦ ⊥
  have _ : ∀ i, DiscreteTopology (M ⧸ h.submodule i) := fun _ ↦ ⟨rfl⟩
  let _ := h.topology
  exact h.isClosedEmbedding_pi.compactSpace

/-- A module is Hausdorff for the inverse-limit topology of a finite quotient system: it embeds in
the Hausdorff product of its discrete quotients. -/
theorem t2Space : @T2Space M h.topology := by
  let _ : ∀ i, TopologicalSpace (M ⧸ h.submodule i) := fun _ ↦ ⊥
  have _ : ∀ i, DiscreteTopology (M ⧸ h.submodule i) := fun _ ↦ ⟨rfl⟩
  let _ := h.topology
  exact h.isClosedEmbedding_pi.isEmbedding.t2Space

end Topology

/-- A module that is finite as a set carries the one-term finite quotient system `J = ⊥`. -/
def ofFinite [_root_.Finite M] (U : Module.End R M) : U.FiniteQuotientSystem Unit where
  submodule _ := ⊥
  directed _ _ := ⟨(), le_rfl, le_rfl⟩
  le_comap _ := bot_le
  finite_quotient _ := _root_.Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  iInf_eq_bot := iInf_const
  exists_sModEq x _ := ⟨x (), fun _ ↦ SModEq.rfl⟩

@[simp]
theorem ofFinite_submodule [_root_.Finite M] (U : Module.End R M) (i : Unit) :
    (ofFinite U).submodule i = ⊥ :=
  (rfl)

/-- A nonzero module over an infinite division ring has no finite quotient system: a proper
quotient is a nonzero vector space, hence infinite, so every member of a system would be `⊤`. -/
theorem isEmpty_of_infinite {K : Type*} [DivisionRing K] [Infinite K] [Module K M] [Nontrivial M]
    (U : Module.End K M) (ι : Type*) : IsEmpty (U.FiniteQuotientSystem ι) := by
  refine ⟨fun h ↦ ?_⟩
  have htop : ∀ i, h.submodule i = ⊤ := fun i ↦ by
    by_contra hne
    have : Nontrivial (M ⧸ h.submodule i) := Submodule.Quotient.nontrivial_iff.2 hne
    have := Module.Free.infinite K (M ⧸ h.submodule i)
    exact not_finite (M ⧸ h.submodule i)
  have hbot := h.iInf_eq_bot
  simp only [htop, iInf_top] at hbot
  exact top_ne_bot hbot

end FiniteQuotientSystem

end Ring

namespace FiniteQuotientSystem

variable [CommRing R] [Module R M]

/-- The `I`-adic filtration `(I ^ n • ⊤)ₙ` of an `I`-adically complete module whose quotients
`M ⧸ I ^ n • ⊤` are finite is a finite quotient system for every endomorphism. -/
def ofIsAdicComplete (I : Ideal R) [IsAdicComplete I M]
    (hfin : ∀ n, _root_.Finite (M ⧸ (I ^ n • ⊤ : Submodule R M))) (U : Module.End R M) :
    U.FiniteQuotientSystem ℕ where
  submodule n := I ^ n • ⊤
  directed := Antitone.directed_ge fun _ _ hmn ↦ smul_mono_left (Ideal.pow_le_pow_right hmn)
  le_comap n := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact smul_mono_right _ le_top
  finite_quotient := hfin
  iInf_eq_bot := IsHausdorff.iInf_pow_smul inferInstance
  exists_sModEq x hx := IsPrecomplete.prec inferInstance fun {m n} hmn ↦
    (hx n m (smul_mono_left (Ideal.pow_le_pow_right hmn))).symm

@[simp]
theorem ofIsAdicComplete_submodule (I : Ideal R) [IsAdicComplete I M]
    (hfin : ∀ n, _root_.Finite (M ⧸ (I ^ n • ⊤ : Submodule R M))) (U : Module.End R M) (n : ℕ) :
    (ofIsAdicComplete I hfin U).submodule n = I ^ n • ⊤ :=
  (rfl)

/-- For a finitely generated ideal `I` with `R ⧸ I` finite, the `I`-adic filtration of an
`I`-adically complete finite module is a finite quotient system for every endomorphism. -/
def ofModuleFinite (I : Ideal R) (hI : I.FG) [_root_.Finite (R ⧸ I)] [Module.Finite R M]
    [IsAdicComplete I M] (U : Module.End R M) : U.FiniteQuotientSystem ℕ :=
  ofIsAdicComplete I (fun n ↦ by
    have := Ideal.finite_quotient_pow hI n
    have : _root_.Finite (M ⧸ (⊤ : Submodule R M)) := Finite.of_subsingleton
    exact finite_quotient_smul (I ^ n) Module.Finite.fg_top) U

@[simp]
theorem ofModuleFinite_submodule (I : Ideal R) (hI : I.FG) [_root_.Finite (R ⧸ I)]
    [Module.Finite R M] [IsAdicComplete I M] (U : Module.End R M) (n : ℕ) :
    (ofModuleFinite I hI U).submodule n = I ^ n • ⊤ :=
  (rfl)

end FiniteQuotientSystem

end Module.End
