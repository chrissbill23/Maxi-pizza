# Dichiarazione insiemi
set Pizze; #insieme delle pizze
set Giorni ordered; #insieme dei giorni di apertura della pizzeria
set Fornitori; #insieme dei fornitori
set Materie; #insieme delle materie prime
set Orari; #insieme degli orari di lavoro
set Lavoratori; #insieme dei lavoriatori
set free_cost_Lavoratori within Lavoratori; # lavoratori a costo zero

# Dichiarazione parametri
param G >= 0; # investimento iniziale
param costi_fissi >= 0; # costo fisso mensile in euro
param costi_fissi_ing >= 0; # costo fisso settimanale in euro per ingredienti
param P{Pizze}; # prezzo in euro della pizza i
param Q_st{Pizze, Giorni}; # domanda minima, corrispondente alla quantia' minima di pizza venduta il giorno
param Pr{Fornitori, Materie}; # prezzo in euro di materia del fornitore
param Ing{Materie}; # quantità in grammi di ingrediente m, necessari alla preparazione di una pizza
param Perc_inv; # porzione massima da detrarre dal guadagno giornaliero 
				# precedente per corprire i costi del giorno successivo
param scontoC; # sconto in euro offerto dal fornitore C
param cond_scontoC; # quantità in  kg di pomodoro da pagare per lo scontoC 
param scontoD; # sconto in euro offerto dal fornitore D
param cond_scontoD; # spesa in euro in mozzarella richiesta per lo scontoD
param scontoPizza; # percentuale di sconto su pizze
param maxSconti; # Numero massimo di tipologie di pizza che può scontare
param IncrDPizza{Pizze}; # percentuale massima di aumento della domanda della pizza scontata
param den{Orari, Giorni}; # densità della domanda nell'orario h del giorno j
param paga; # stipendio del pizzaiolo dipendente in euro/ora
param max_pizza{Lavoratori}; # quantità massima di pizze che può fare il pizzaiolo W in un'ora
param T; #Parametro di conversione da chilogrammi a grammi
# big M
param bigM > 0;

# Dichiarazione variabili
var g{Giorni} >= 0; #guadagno in euro del giorno
var qt{Pizze, Giorni} >= 0 integer; #quantità massima di pizza i venduta il giorno j
var qting{Fornitori, Materie, Giorni} >= 0; #quantità in kg di Materie da acquistare da Fornitori in Giorni
var b{Fornitori, Materie, Giorni} binary;# 1 se compra m da f il giorno j. 0 altrimenti
var sconD{Giorni} binary;# 1 se aderisce allo sconto di D il giorno j. 0 altrimenti
var sconC{Giorni} binary;# 1 se aderisce allo sconto di C il giorno j. 0 altrimenti
var r{Materie,Giorni} >= 0;# quantità in grammi di Materie non utilizzata il giorno Giorni
var s{Pizze, Giorni} binary;# 1 se sconta Pizze il giorno j. 0 altrimenti
var deltas{Pizze, Giorni} >= 0; #differenza di ricavo di Pizze scontata il giorno Giorni
var costo_totale_variabile{Giorni} >= 0; #totale costi variabili di Giorni
var l {Lavoratori,Orari,Giorni} binary;# 1 se lavora Lavoratori in Orari del Giorni. 0 altrimenti
 
# Funzione obbiettivo
maximize GuadagnoSettimanale:  sum{j in Giorni}g[j] - (1/4) * costi_fissi - costi_fissi_ing;

# Vincoli

s.t. guadagno_giornaliero{j in Giorni}: sum{i in Pizze}(P[i]*qt[i,j] - deltas[i, j] )
		- costo_totale_variabile[j] = g[j];
		
s.t. totale_costi_variabili_giornalieri{j in Giorni}: costo_totale_variabile[j] = paga * (sum{h in Orari}(sum{w in Lavoratori : w not in free_cost_Lavoratori}l[w, h, j]))
								 + sum{f in Fornitori, m in Materie}Pr[f,m] * qting[f, m, j]
								 - sconD[j] * scontoD - sconC[j] * scontoC;	
								 							 
s.t. upperbound_cost_variab {j in Giorni}: costo_totale_variabile[j] <= (if j-1 == 0
																	then G
																	else Perc_inv * g[j-1]);
																		
s.t. delta_ricavo{i in Pizze, j in Giorni}: deltas[i, j] <=  scontoPizza * P[i] * qt[i, j];
s.t. delta_ricavo_2{i in Pizze, j in Giorni}: deltas[i, j] >=  scontoPizza * P[i] * qt[i, j] - (1-s[i, j]) * bigM;

s.t. maxsconto{j in Giorni}: sum{i in Pizze} s[i,j] <= maxSconti;

s.t. ingr_necessari{m in Materie, j in Giorni}:  Ing[m] * sum{i in Pizze}qt[i, j] <=  T * sum{f in Fornitori} qting[f, m, j] + (if j-1 == 0
																																	then 0
																																	else r[m,j-1]);
s.t. quantita_ingr_forn{f in Fornitori, m in Materie, j in Giorni}: qting[f, m, j] <= b[f, m, j] * bigM;
s.t. quantita_ingr_forn2{f in Fornitori, m in Materie, j in Giorni}: qting[f, m, j] >= b[f, m, j]; 
s.t. cond_fornB_2{j in Giorni}: b['B','fa',j] = b['B','pom',j];

s.t. cond_sconto_pom {j in Giorni}: qting['C', 'pom', j] >= sconC[j] * cond_scontoC;
s.t. cond_sconto_moz{j in Giorni}: Pr['D','moz'] * qting['D', 'moz', j] >= sconD[j] * cond_scontoD;

s.t. quantita_desiderata{ i in Pizze, j in Giorni}: qt[i, j] >= Q_st[i, j];
s.t. quantita_desiderata_2{ i in Pizze, j in Giorni}: qt[i, j] <= Q_st[i, j] + IncrDPizza[i] * Q_st[i, j] * s[i, j];

s.t. upper_bound_quantita{h in Orari, j in Giorni}: den[h,j] * sum{i in Pizze}qt[i,j] <= sum{w in Lavoratori}max_pizza[w] * l[w,h,j];

s.t. resti_materie{ m in Materie, j in Giorni}: r[m,j] = T * sum{f in Fornitori}qting[f, m, j] - Ing[m] * sum{i in Pizze}qt[i, j] + (if j-1 == 0
																													            		then 0
																																		else r[m,j-1]) ;
s.t. resti_materie_dom{ m in Materie}: r[m,6] = 0 ;																																	

